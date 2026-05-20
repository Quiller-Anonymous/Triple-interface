import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [50,51). -/

/- Block 050 covers tail-support indices [1250,1275) and q from 2110 to 2147. -/

def TailChunk000Sub000Block050Part000SupportExplicit : Finset ℕ :=
  ([2110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part000 : ℚ :=
  (3173239 : ℚ) / 14408881200

def SurrogateDiagonalTailChunk000Sub000Block050Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2110
    = surrogateDiagTailX0RatChunk000Sub000Block050Part000

theorem surrogateDiagonalTailChunk000Sub000Block050Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part000] using hcert

def TailChunk000Sub000Block050Part001SupportExplicit : Finset ℕ :=
  ([2111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part001 : ℚ :=
  (11136346179 : ℚ) / 660838621629400

def SurrogateDiagonalTailChunk000Sub000Block050Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2111
    = surrogateDiagTailX0RatChunk000Sub000Block050Part001

theorem surrogateDiagonalTailChunk000Sub000Block050Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part001] using hcert

def TailChunk000Sub000Block050Part002SupportExplicit : Finset ℕ :=
  ([2113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part002 : ℚ :=
  (557984505775 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block050Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2113
    = surrogateDiagTailX0RatChunk000Sub000Block050Part002

theorem surrogateDiagonalTailChunk000Sub000Block050Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part002] using hcert

def TailChunk000Sub000Block050Part003SupportExplicit : Finset ℕ :=
  ([2114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part003 : ℚ :=
  (9807473407 : ℚ) / 65623122000000

def SurrogateDiagonalTailChunk000Sub000Block050Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2114
    = surrogateDiagTailX0RatChunk000Sub000Block050Part003

theorem surrogateDiagonalTailChunk000Sub000Block050Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part003] using hcert

def TailChunk000Sub000Block050Part004SupportExplicit : Finset ℕ :=
  ([2117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part004 : ℚ :=
  (179381623375 : ℚ) / 13767900390752256

def SurrogateDiagonalTailChunk000Sub000Block050Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2117
    = surrogateDiagTailX0RatChunk000Sub000Block050Part004

theorem surrogateDiagonalTailChunk000Sub000Block050Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part004] using hcert

def TailChunk000Sub000Block050Part005SupportExplicit : Finset ℕ :=
  ([2118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part005 : ℚ :=
  (9181893775 : ℚ) / 27918675738624

def SurrogateDiagonalTailChunk000Sub000Block050Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2118
    = surrogateDiagTailX0RatChunk000Sub000Block050Part005

theorem surrogateDiagonalTailChunk000Sub000Block050Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part005] using hcert

def TailChunk000Sub000Block050Part006SupportExplicit : Finset ℕ :=
  ([2119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part006 : ℚ :=
  (379185136475 : ℚ) / 17855906600346624

def SurrogateDiagonalTailChunk000Sub000Block050Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2119
    = surrogateDiagTailX0RatChunk000Sub000Block050Part006

theorem surrogateDiagonalTailChunk000Sub000Block050Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part006] using hcert

def TailChunk000Sub000Block050Part007SupportExplicit : Finset ℕ :=
  ([2121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part007 : ℚ :=
  (8300161967 : ℚ) / 103700736000000

def SurrogateDiagonalTailChunk000Sub000Block050Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2121
    = surrogateDiagTailX0RatChunk000Sub000Block050Part007

theorem surrogateDiagonalTailChunk000Sub000Block050Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part007] using hcert

def TailChunk000Sub000Block050Part008SupportExplicit : Finset ℕ :=
  ([2122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part008 : ℚ :=
  (5625227837 : ℚ) / 63136472769600

def SurrogateDiagonalTailChunk000Sub000Block050Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2122
    = surrogateDiagTailX0RatChunk000Sub000Block050Part008

theorem surrogateDiagonalTailChunk000Sub000Block050Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part008] using hcert

def TailChunk000Sub000Block050Part009SupportExplicit : Finset ℕ :=
  ([2123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part009 : ℚ :=
  (20772247591 : ℚ) / 1359226286899200

def SurrogateDiagonalTailChunk000Sub000Block050Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2123
    = surrogateDiagTailX0RatChunk000Sub000Block050Part009

theorem surrogateDiagonalTailChunk000Sub000Block050Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part009] using hcert

def TailChunk000Sub000Block050Part010SupportExplicit : Finset ℕ :=
  ([2126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part010 : ℚ :=
  (176416410125 : ℚ) / 1590358118442084

def SurrogateDiagonalTailChunk000Sub000Block050Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2126
    = surrogateDiagTailX0RatChunk000Sub000Block050Part010

theorem surrogateDiagonalTailChunk000Sub000Block050Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part010] using hcert

def TailChunk000Sub000Block050Part011SupportExplicit : Finset ℕ :=
  ([2127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part011 : ℚ :=
  (203988304625 : ℚ) / 5026317016310784

def SurrogateDiagonalTailChunk000Sub000Block050Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2127
    = surrogateDiagTailX0RatChunk000Sub000Block050Part011

theorem surrogateDiagonalTailChunk000Sub000Block050Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part011] using hcert

def TailChunk000Sub000Block050Part012SupportExplicit : Finset ℕ :=
  ([2129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part012 : ℚ :=
  (5779117275 : ℚ) / 348815695642624

def SurrogateDiagonalTailChunk000Sub000Block050Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2129
    = surrogateDiagTailX0RatChunk000Sub000Block050Part012

theorem surrogateDiagonalTailChunk000Sub000Block050Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part012] using hcert

def TailChunk000Sub000Block050Part013SupportExplicit : Finset ℕ :=
  ([2130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part013 : ℚ :=
  (3565700483 : ℚ) / 4918231449600

def SurrogateDiagonalTailChunk000Sub000Block050Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2130
    = surrogateDiagTailX0RatChunk000Sub000Block050Part013

theorem surrogateDiagonalTailChunk000Sub000Block050Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part013] using hcert

def TailChunk000Sub000Block050Part014SupportExplicit : Finset ℕ :=
  ([2131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part014 : ℚ :=
  (22701263839 : ℚ) / 2058757830232200

def SurrogateDiagonalTailChunk000Sub000Block050Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2131
    = surrogateDiagTailX0RatChunk000Sub000Block050Part014

theorem surrogateDiagonalTailChunk000Sub000Block050Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part014] using hcert

def TailChunk000Sub000Block050Part015SupportExplicit : Finset ℕ :=
  ([2134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part015 : ℚ :=
  (12729131641 : ℚ) / 84951642931200

def SurrogateDiagonalTailChunk000Sub000Block050Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2134
    = surrogateDiagTailX0RatChunk000Sub000Block050Part015

theorem surrogateDiagonalTailChunk000Sub000Block050Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part015] using hcert

def TailChunk000Sub000Block050Part016SupportExplicit : Finset ℕ :=
  ([2135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part016 : ℚ :=
  (1368894761 : ℚ) / 35838974361600

def SurrogateDiagonalTailChunk000Sub000Block050Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2135
    = surrogateDiagTailX0RatChunk000Sub000Block050Part016

theorem surrogateDiagonalTailChunk000Sub000Block050Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part016] using hcert

def TailChunk000Sub000Block050Part017SupportExplicit : Finset ℕ :=
  ([2137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part017 : ℚ :=
  (95102964425 : ℚ) / 5783481395546112

def SurrogateDiagonalTailChunk000Sub000Block050Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2137
    = surrogateDiagTailX0RatChunk000Sub000Block050Part017

theorem surrogateDiagonalTailChunk000Sub000Block050Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part017] using hcert

def TailChunk000Sub000Block050Part018SupportExplicit : Finset ℕ :=
  ([2138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part018 : ℚ :=
  (178413561125 : ℚ) / 1626604142497344

def SurrogateDiagonalTailChunk000Sub000Block050Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2138
    = surrogateDiagTailX0RatChunk000Sub000Block050Part018

theorem surrogateDiagonalTailChunk000Sub000Block050Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part018] using hcert

def TailChunk000Sub000Block050Part019SupportExplicit : Finset ℕ :=
  ([2139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part019 : ℚ :=
  (18645198133 : ℚ) / 303656495155200

def SurrogateDiagonalTailChunk000Sub000Block050Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2139
    = surrogateDiagTailX0RatChunk000Sub000Block050Part019

theorem surrogateDiagonalTailChunk000Sub000Block050Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part019] using hcert

def TailChunk000Sub000Block050Part020SupportExplicit : Finset ℕ :=
  ([2141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part020 : ℚ :=
  (22914821119 : ℚ) / 2097693070723200

def SurrogateDiagonalTailChunk000Sub000Block050Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2141
    = surrogateDiagTailX0RatChunk000Sub000Block050Part020

theorem surrogateDiagonalTailChunk000Sub000Block050Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part020] using hcert

def TailChunk000Sub000Block050Part021SupportExplicit : Finset ℕ :=
  ([2143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part021 : ℚ :=
  (573941313775 : ℚ) / 52638647851685448

def SurrogateDiagonalTailChunk000Sub000Block050Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2143
    = surrogateDiagTailX0RatChunk000Sub000Block050Part021

theorem surrogateDiagonalTailChunk000Sub000Block050Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part021] using hcert

def TailChunk000Sub000Block050Part022SupportExplicit : Finset ℕ :=
  ([2145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part022 : ℚ :=
  (575196413 : ℚ) / 4247582146560

def SurrogateDiagonalTailChunk000Sub000Block050Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2145
    = surrogateDiagTailX0RatChunk000Sub000Block050Part022

theorem surrogateDiagonalTailChunk000Sub000Block050Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part022] using hcert

def TailChunk000Sub000Block050Part023SupportExplicit : Finset ℕ :=
  ([2146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part023 : ℚ :=
  (48084594175 : ℚ) / 368783046180864

def SurrogateDiagonalTailChunk000Sub000Block050Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2146
    = surrogateDiagTailX0RatChunk000Sub000Block050Part023

theorem surrogateDiagonalTailChunk000Sub000Block050Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part023] using hcert

def TailChunk000Sub000Block050Part024SupportExplicit : Finset ℕ :=
  ([2147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block050Part024 : ℚ :=
  (200167871725 : ℚ) / 10325925293064192

def SurrogateDiagonalTailChunk000Sub000Block050Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2147
    = surrogateDiagTailX0RatChunk000Sub000Block050Part024

theorem surrogateDiagonalTailChunk000Sub000Block050Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block050Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block050Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block050Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block050Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block050Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block050Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block050HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block050Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block050Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block050Part000
    + surrogateDiagTailX0RatChunk000Sub000Block050Part001
    + surrogateDiagTailX0RatChunk000Sub000Block050Part002
    + surrogateDiagTailX0RatChunk000Sub000Block050Part003
    + surrogateDiagTailX0RatChunk000Sub000Block050Part004
    + surrogateDiagTailX0RatChunk000Sub000Block050Part005
    + surrogateDiagTailX0RatChunk000Sub000Block050Part006
    + surrogateDiagTailX0RatChunk000Sub000Block050Part007
    + surrogateDiagTailX0RatChunk000Sub000Block050Part008
    + surrogateDiagTailX0RatChunk000Sub000Block050Part009

def surrogateDiagonalTailChunk000Sub000Block050MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block050Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block050Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block050Part010
    + surrogateDiagTailX0RatChunk000Sub000Block050Part011
    + surrogateDiagTailX0RatChunk000Sub000Block050Part012
    + surrogateDiagTailX0RatChunk000Sub000Block050Part013
    + surrogateDiagTailX0RatChunk000Sub000Block050Part014
    + surrogateDiagTailX0RatChunk000Sub000Block050Part015
    + surrogateDiagTailX0RatChunk000Sub000Block050Part016
    + surrogateDiagTailX0RatChunk000Sub000Block050Part017
    + surrogateDiagTailX0RatChunk000Sub000Block050Part018
    + surrogateDiagTailX0RatChunk000Sub000Block050Part019

def surrogateDiagonalTailChunk000Sub000Block050TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block050Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block050Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block050Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block050Part020
    + surrogateDiagTailX0RatChunk000Sub000Block050Part021
    + surrogateDiagTailX0RatChunk000Sub000Block050Part022
    + surrogateDiagTailX0RatChunk000Sub000Block050Part023
    + surrogateDiagTailX0RatChunk000Sub000Block050Part024

def surrogateDiagonalTailChunk000Sub000Block050Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block050HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block050MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block050TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block050 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block050Part000
    + surrogateDiagTailX0RatChunk000Sub000Block050Part001
    + surrogateDiagTailX0RatChunk000Sub000Block050Part002
    + surrogateDiagTailX0RatChunk000Sub000Block050Part003
    + surrogateDiagTailX0RatChunk000Sub000Block050Part004
    + surrogateDiagTailX0RatChunk000Sub000Block050Part005
    + surrogateDiagTailX0RatChunk000Sub000Block050Part006
    + surrogateDiagTailX0RatChunk000Sub000Block050Part007
    + surrogateDiagTailX0RatChunk000Sub000Block050Part008
    + surrogateDiagTailX0RatChunk000Sub000Block050Part009
    + surrogateDiagTailX0RatChunk000Sub000Block050Part010
    + surrogateDiagTailX0RatChunk000Sub000Block050Part011
    + surrogateDiagTailX0RatChunk000Sub000Block050Part012
    + surrogateDiagTailX0RatChunk000Sub000Block050Part013
    + surrogateDiagTailX0RatChunk000Sub000Block050Part014
    + surrogateDiagTailX0RatChunk000Sub000Block050Part015
    + surrogateDiagTailX0RatChunk000Sub000Block050Part016
    + surrogateDiagTailX0RatChunk000Sub000Block050Part017
    + surrogateDiagTailX0RatChunk000Sub000Block050Part018
    + surrogateDiagTailX0RatChunk000Sub000Block050Part019
    + surrogateDiagTailX0RatChunk000Sub000Block050Part020
    + surrogateDiagTailX0RatChunk000Sub000Block050Part021
    + surrogateDiagTailX0RatChunk000Sub000Block050Part022
    + surrogateDiagTailX0RatChunk000Sub000Block050Part023
    + surrogateDiagTailX0RatChunk000Sub000Block050Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block050_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block050Head + surrogateDiagTailX0RatChunk000Sub000Block050Mid + surrogateDiagTailX0RatChunk000Sub000Block050Tail =
      surrogateDiagTailX0RatChunk000Sub000Block050 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block050Head surrogateDiagTailX0RatChunk000Sub000Block050Mid surrogateDiagTailX0RatChunk000Sub000Block050Tail surrogateDiagTailX0RatChunk000Sub000Block050
  ring

def SurrogateDiagonalTailChunk000Sub000Block050HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block050HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block050Head

def SurrogateDiagonalTailChunk000Sub000Block050MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block050MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block050Mid

def SurrogateDiagonalTailChunk000Sub000Block050TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block050TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block050Tail

theorem surrogateDiagonalTailChunk000Sub000Block050_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block050HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block050MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block050TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block050Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block050 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block050HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block050MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block050TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block050Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block050_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
