import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [22,23). -/

/- Block 022 covers tail-support indices [550,575) and q from 957 to 995. -/

def TailChunk000Sub000Block022Part000SupportExplicit : Finset ℕ :=
  ([957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part000 : ℚ :=
  (6930808093 : ℚ) / 9836462899200

def SurrogateDiagonalTailChunk000Sub000Block022Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 957
    = surrogateDiagTailX0RatChunk000Sub000Block022Part000

theorem surrogateDiagonalTailChunk000Sub000Block022Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part000] using hcert

def TailChunk000Sub000Block022Part001SupportExplicit : Finset ℕ :=
  ([958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part001 : ℚ :=
  (157425206125 : ℚ) / 130538448109128

def SurrogateDiagonalTailChunk000Sub000Block022Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 958
    = surrogateDiagTailX0RatChunk000Sub000Block022Part001

theorem surrogateDiagonalTailChunk000Sub000Block022Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part001] using hcert

def TailChunk000Sub000Block022Part002SupportExplicit : Finset ℕ :=
  ([959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part002 : ℚ :=
  (246981656125 : ℚ) / 1108632213946368

def SurrogateDiagonalTailChunk000Sub000Block022Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 959
    = surrogateDiagTailX0RatChunk000Sub000Block022Part002

theorem surrogateDiagonalTailChunk000Sub000Block022Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part002] using hcert

def TailChunk000Sub000Block022Part003SupportExplicit : Finset ℕ :=
  ([962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part003 : ℚ :=
  (4831345375 : ℚ) / 3225507692544

def SurrogateDiagonalTailChunk000Sub000Block022Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 962
    = surrogateDiagTailX0RatChunk000Sub000Block022Part003

theorem surrogateDiagonalTailChunk000Sub000Block022Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part003] using hcert

def TailChunk000Sub000Block022Part004SupportExplicit : Finset ℕ :=
  ([965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part004 : ℚ :=
  (233994992125 : ℚ) / 869904823615488

def SurrogateDiagonalTailChunk000Sub000Block022Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 965
    = surrogateDiagTailX0RatChunk000Sub000Block022Part004

theorem surrogateDiagonalTailChunk000Sub000Block022Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part004] using hcert

def TailChunk000Sub000Block022Part005SupportExplicit : Finset ℕ :=
  ([966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part005 : ℚ :=
  (3010607075 : ℚ) / 449861474304

def SurrogateDiagonalTailChunk000Sub000Block022Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 966
    = surrogateDiagTailX0RatChunk000Sub000Block022Part005

theorem surrogateDiagonalTailChunk000Sub000Block022Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part005] using hcert

def TailChunk000Sub000Block022Part006SupportExplicit : Finset ℕ :=
  ([967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part006 : ℚ :=
  (145990770125 : ℚ) / 1088692845450084

def SurrogateDiagonalTailChunk000Sub000Block022Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 967
    = surrogateDiagTailX0RatChunk000Sub000Block022Part006

theorem surrogateDiagonalTailChunk000Sub000Block022Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part006] using hcert

def TailChunk000Sub000Block022Part007SupportExplicit : Finset ℕ :=
  ([969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part007 : ℚ :=
  (32615838425 : ℚ) / 45873887182848

def SurrogateDiagonalTailChunk000Sub000Block022Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 969
    = surrogateDiagTailX0RatChunk000Sub000Block022Part007

theorem surrogateDiagonalTailChunk000Sub000Block022Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part007] using hcert

def TailChunk000Sub000Block022Part008SupportExplicit : Finset ℕ :=
  ([970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part008 : ℚ :=
  (126253653775 : ℚ) / 54369051475968

def SurrogateDiagonalTailChunk000Sub000Block022Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 970
    = surrogateDiagTailX0RatChunk000Sub000Block022Part008

theorem surrogateDiagonalTailChunk000Sub000Block022Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part008] using hcert

def TailChunk000Sub000Block022Part009SupportExplicit : Finset ℕ :=
  ([971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part009 : ℚ :=
  (941898159 : ℚ) / 5903132457080

def SurrogateDiagonalTailChunk000Sub000Block022Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 971
    = surrogateDiagTailX0RatChunk000Sub000Block022Part009

theorem surrogateDiagonalTailChunk000Sub000Block022Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part009] using hcert

def TailChunk000Sub000Block022Part010SupportExplicit : Finset ℕ :=
  ([973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part010 : ℚ :=
  (2728803125 : ℚ) / 10882394123616

def SurrogateDiagonalTailChunk000Sub000Block022Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 973
    = surrogateDiagTailX0RatChunk000Sub000Block022Part010

theorem surrogateDiagonalTailChunk000Sub000Block022Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part010] using hcert

def TailChunk000Sub000Block022Part011SupportExplicit : Finset ℕ :=
  ([974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part011 : ℚ :=
  (147963809875 : ℚ) / 139499270315208

def SurrogateDiagonalTailChunk000Sub000Block022Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 974
    = surrogateDiagTailX0RatChunk000Sub000Block022Part011

theorem surrogateDiagonalTailChunk000Sub000Block022Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part011] using hcert

def TailChunk000Sub000Block022Part012SupportExplicit : Finset ℕ :=
  ([977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part012 : ℚ :=
  (149025840125 : ℚ) / 1134478144978944

def SurrogateDiagonalTailChunk000Sub000Block022Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 977
    = surrogateDiagTailX0RatChunk000Sub000Block022Part012

theorem surrogateDiagonalTailChunk000Sub000Block022Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part012] using hcert

def TailChunk000Sub000Block022Part013SupportExplicit : Finset ℕ :=
  ([978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part013 : ℚ :=
  (25174091425 : ℚ) / 6888852855072

def SurrogateDiagonalTailChunk000Sub000Block022Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 978
    = surrogateDiagTailX0RatChunk000Sub000Block022Part013

theorem surrogateDiagonalTailChunk000Sub000Block022Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part013] using hcert

def TailChunk000Sub000Block022Part014SupportExplicit : Finset ℕ :=
  ([979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part014 : ℚ :=
  (10812600529 : ℚ) / 59981529907200

def SurrogateDiagonalTailChunk000Sub000Block022Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 979
    = surrogateDiagTailX0RatChunk000Sub000Block022Part014

theorem surrogateDiagonalTailChunk000Sub000Block022Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part014] using hcert

def TailChunk000Sub000Block022Part015SupportExplicit : Finset ℕ :=
  ([982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part015 : ℚ :=
  (171890753 : ℚ) / 164741541720

def SurrogateDiagonalTailChunk000Sub000Block022Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 982
    = surrogateDiagTailX0RatChunk000Sub000Block022Part015

theorem surrogateDiagonalTailChunk000Sub000Block022Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part015] using hcert

def TailChunk000Sub000Block022Part016SupportExplicit : Finset ℕ :=
  ([983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part016 : ℚ :=
  (150861870125 : ℚ) / 1162633451414244

def SurrogateDiagonalTailChunk000Sub000Block022Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 983
    = surrogateDiagTailX0RatChunk000Sub000Block022Part016

theorem surrogateDiagonalTailChunk000Sub000Block022Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part016] using hcert

def TailChunk000Sub000Block022Part017SupportExplicit : Finset ℕ :=
  ([985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part017 : ℚ :=
  (120696509375 : ℚ) / 472346948419584

def SurrogateDiagonalTailChunk000Sub000Block022Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 985
    = surrogateDiagTailX0RatChunk000Sub000Block022Part017

theorem surrogateDiagonalTailChunk000Sub000Block022Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part017] using hcert

def TailChunk000Sub000Block022Part018SupportExplicit : Finset ℕ :=
  ([986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part018 : ℚ :=
  (34558416475 : ℚ) / 25181345021952

def SurrogateDiagonalTailChunk000Sub000Block022Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 986
    = surrogateDiagTailX0RatChunk000Sub000Block022Part018

theorem surrogateDiagonalTailChunk000Sub000Block022Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part018] using hcert

def TailChunk000Sub000Block022Part019SupportExplicit : Finset ℕ :=
  ([987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part019 : ℚ :=
  (85235686175 : ℚ) / 116078870651904

def SurrogateDiagonalTailChunk000Sub000Block022Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 987
    = surrogateDiagTailX0RatChunk000Sub000Block022Part019

theorem surrogateDiagonalTailChunk000Sub000Block022Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part019] using hcert

def TailChunk000Sub000Block022Part020SupportExplicit : Finset ℕ :=
  ([989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part020 : ℚ :=
  (5105626775 : ℚ) / 32548180574448

def SurrogateDiagonalTailChunk000Sub000Block022Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 989
    = surrogateDiagTailX0RatChunk000Sub000Block022Part020

theorem surrogateDiagonalTailChunk000Sub000Block022Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part020] using hcert

def TailChunk000Sub000Block022Part021SupportExplicit : Finset ℕ :=
  ([991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part021 : ℚ :=
  (1226619169 : ℚ) / 9607881292020

def SurrogateDiagonalTailChunk000Sub000Block022Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 991
    = surrogateDiagTailX0RatChunk000Sub000Block022Part021

theorem surrogateDiagonalTailChunk000Sub000Block022Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part021] using hcert

def TailChunk000Sub000Block022Part022SupportExplicit : Finset ℕ :=
  ([993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part022 : ℚ :=
  (91027 : ℚ) / 210830400

def SurrogateDiagonalTailChunk000Sub000Block022Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 993
    = surrogateDiagTailX0RatChunk000Sub000Block022Part022

theorem surrogateDiagonalTailChunk000Sub000Block022Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part022] using hcert

def TailChunk000Sub000Block022Part023SupportExplicit : Finset ℕ :=
  ([994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part023 : ℚ :=
  (82856687 : ℚ) / 49401878400

def SurrogateDiagonalTailChunk000Sub000Block022Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 994
    = surrogateDiagTailX0RatChunk000Sub000Block022Part023

theorem surrogateDiagonalTailChunk000Sub000Block022Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part023] using hcert

def TailChunk000Sub000Block022Part024SupportExplicit : Finset ℕ :=
  ([995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block022Part024 : ℚ :=
  (123159501875 : ℚ) / 491923522151424

def SurrogateDiagonalTailChunk000Sub000Block022Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 995
    = surrogateDiagTailX0RatChunk000Sub000Block022Part024

theorem surrogateDiagonalTailChunk000Sub000Block022Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block022Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block022Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block022Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block022Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block022Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block022Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block022HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block022Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block022Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block022Part000
    + surrogateDiagTailX0RatChunk000Sub000Block022Part001
    + surrogateDiagTailX0RatChunk000Sub000Block022Part002
    + surrogateDiagTailX0RatChunk000Sub000Block022Part003
    + surrogateDiagTailX0RatChunk000Sub000Block022Part004
    + surrogateDiagTailX0RatChunk000Sub000Block022Part005
    + surrogateDiagTailX0RatChunk000Sub000Block022Part006
    + surrogateDiagTailX0RatChunk000Sub000Block022Part007
    + surrogateDiagTailX0RatChunk000Sub000Block022Part008
    + surrogateDiagTailX0RatChunk000Sub000Block022Part009

def surrogateDiagonalTailChunk000Sub000Block022MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block022Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block022Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block022Part010
    + surrogateDiagTailX0RatChunk000Sub000Block022Part011
    + surrogateDiagTailX0RatChunk000Sub000Block022Part012
    + surrogateDiagTailX0RatChunk000Sub000Block022Part013
    + surrogateDiagTailX0RatChunk000Sub000Block022Part014
    + surrogateDiagTailX0RatChunk000Sub000Block022Part015
    + surrogateDiagTailX0RatChunk000Sub000Block022Part016
    + surrogateDiagTailX0RatChunk000Sub000Block022Part017
    + surrogateDiagTailX0RatChunk000Sub000Block022Part018
    + surrogateDiagTailX0RatChunk000Sub000Block022Part019

def surrogateDiagonalTailChunk000Sub000Block022TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block022Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block022Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block022Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block022Part020
    + surrogateDiagTailX0RatChunk000Sub000Block022Part021
    + surrogateDiagTailX0RatChunk000Sub000Block022Part022
    + surrogateDiagTailX0RatChunk000Sub000Block022Part023
    + surrogateDiagTailX0RatChunk000Sub000Block022Part024

def surrogateDiagonalTailChunk000Sub000Block022Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block022HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block022MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block022TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block022 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block022Part000
    + surrogateDiagTailX0RatChunk000Sub000Block022Part001
    + surrogateDiagTailX0RatChunk000Sub000Block022Part002
    + surrogateDiagTailX0RatChunk000Sub000Block022Part003
    + surrogateDiagTailX0RatChunk000Sub000Block022Part004
    + surrogateDiagTailX0RatChunk000Sub000Block022Part005
    + surrogateDiagTailX0RatChunk000Sub000Block022Part006
    + surrogateDiagTailX0RatChunk000Sub000Block022Part007
    + surrogateDiagTailX0RatChunk000Sub000Block022Part008
    + surrogateDiagTailX0RatChunk000Sub000Block022Part009
    + surrogateDiagTailX0RatChunk000Sub000Block022Part010
    + surrogateDiagTailX0RatChunk000Sub000Block022Part011
    + surrogateDiagTailX0RatChunk000Sub000Block022Part012
    + surrogateDiagTailX0RatChunk000Sub000Block022Part013
    + surrogateDiagTailX0RatChunk000Sub000Block022Part014
    + surrogateDiagTailX0RatChunk000Sub000Block022Part015
    + surrogateDiagTailX0RatChunk000Sub000Block022Part016
    + surrogateDiagTailX0RatChunk000Sub000Block022Part017
    + surrogateDiagTailX0RatChunk000Sub000Block022Part018
    + surrogateDiagTailX0RatChunk000Sub000Block022Part019
    + surrogateDiagTailX0RatChunk000Sub000Block022Part020
    + surrogateDiagTailX0RatChunk000Sub000Block022Part021
    + surrogateDiagTailX0RatChunk000Sub000Block022Part022
    + surrogateDiagTailX0RatChunk000Sub000Block022Part023
    + surrogateDiagTailX0RatChunk000Sub000Block022Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block022_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block022Head + surrogateDiagTailX0RatChunk000Sub000Block022Mid + surrogateDiagTailX0RatChunk000Sub000Block022Tail =
      surrogateDiagTailX0RatChunk000Sub000Block022 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block022Head surrogateDiagTailX0RatChunk000Sub000Block022Mid surrogateDiagTailX0RatChunk000Sub000Block022Tail surrogateDiagTailX0RatChunk000Sub000Block022
  ring

def SurrogateDiagonalTailChunk000Sub000Block022HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block022HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block022Head

def SurrogateDiagonalTailChunk000Sub000Block022MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block022MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block022Mid

def SurrogateDiagonalTailChunk000Sub000Block022TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block022TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block022Tail

theorem surrogateDiagonalTailChunk000Sub000Block022_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block022HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block022MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block022TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block022Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block022 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block022HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block022MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block022TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block022Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block022_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
