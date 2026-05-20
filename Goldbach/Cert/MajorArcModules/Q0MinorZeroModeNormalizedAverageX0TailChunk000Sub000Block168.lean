import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [168,169). -/

/-- Block 168 covers tail-support indices [4200,4225) and q from 6965 to 7001. -/

def TailChunk000Sub000Block168Part000SupportExplicit : Finset ℕ :=
  ([6965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part000 : ℚ :=
  (941125364225 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub000Block168Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6965
    = surrogateDiagTailX0RatChunk000Sub000Block168Part000

theorem surrogateDiagonalTailChunk000Sub000Block168Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part000] using hcert

def TailChunk000Sub000Block168Part001SupportExplicit : Finset ℕ :=
  ([6967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part001 : ℚ :=
  (758423265625 : ℚ) / 1471976064360813042

def SurrogateDiagonalTailChunk000Sub000Block168Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6967
    = surrogateDiagTailX0RatChunk000Sub000Block168Part001

theorem surrogateDiagonalTailChunk000Sub000Block168Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part001] using hcert

def TailChunk000Sub000Block168Part002SupportExplicit : Finset ℕ :=
  ([6969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part002 : ℚ :=
  (31687998581 : ℚ) / 18744228096000000

def SurrogateDiagonalTailChunk000Sub000Block168Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6969
    = surrogateDiagTailX0RatChunk000Sub000Block168Part002

theorem surrogateDiagonalTailChunk000Sub000Block168Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part002] using hcert

def TailChunk000Sub000Block168Part003SupportExplicit : Finset ℕ :=
  ([6970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part003 : ℚ :=
  (6289643893 : ℚ) / 1073956572364800

def SurrogateDiagonalTailChunk000Sub000Block168Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6970
    = surrogateDiagTailX0RatChunk000Sub000Block168Part003

theorem surrogateDiagonalTailChunk000Sub000Block168Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part003] using hcert

def TailChunk000Sub000Block168Part004SupportExplicit : Finset ℕ :=
  ([6971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part004 : ℚ :=
  (1214871025 : ℚ) / 2360575865578962

def SurrogateDiagonalTailChunk000Sub000Block168Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6971
    = surrogateDiagTailX0RatChunk000Sub000Block168Part004

theorem surrogateDiagonalTailChunk000Sub000Block168Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part004] using hcert

def TailChunk000Sub000Block168Part005SupportExplicit : Finset ℕ :=
  ([6973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part005 : ℚ :=
  (78543672175 : ℚ) / 130839453091526688

def SurrogateDiagonalTailChunk000Sub000Block168Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6973
    = surrogateDiagTailX0RatChunk000Sub000Block168Part005

theorem surrogateDiagonalTailChunk000Sub000Block168Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part005] using hcert

def TailChunk000Sub000Block168Part006SupportExplicit : Finset ℕ :=
  ([6974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part006 : ℚ :=
  (1153517269 : ℚ) / 398928599205888

def SurrogateDiagonalTailChunk000Sub000Block168Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6974
    = surrogateDiagTailX0RatChunk000Sub000Block168Part006

theorem surrogateDiagonalTailChunk000Sub000Block168Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part006] using hcert

def TailChunk000Sub000Block168Part007SupportExplicit : Finset ℕ :=
  ([6977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part007 : ℚ :=
  (760602015625 : ℚ) / 1480446628407017472

def SurrogateDiagonalTailChunk000Sub000Block168Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6977
    = surrogateDiagTailX0RatChunk000Sub000Block168Part007

theorem surrogateDiagonalTailChunk000Sub000Block168Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part007] using hcert

def TailChunk000Sub000Block168Part008SupportExplicit : Finset ℕ :=
  ([6978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part008 : ℚ :=
  (675814145875 : ℚ) / 72940939652316288

def SurrogateDiagonalTailChunk000Sub000Block168Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6978
    = surrogateDiagTailX0RatChunk000Sub000Block168Part008

theorem surrogateDiagonalTailChunk000Sub000Block168Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part008] using hcert

def TailChunk000Sub000Block168Part009SupportExplicit : Finset ℕ :=
  ([6979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part009 : ℚ :=
  (2482358469775 : ℚ) / 3189107905431717888

def SurrogateDiagonalTailChunk000Sub000Block168Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6979
    = surrogateDiagTailX0RatChunk000Sub000Block168Part009

theorem surrogateDiagonalTailChunk000Sub000Block168Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part009] using hcert

def TailChunk000Sub000Block168Part010SupportExplicit : Finset ℕ :=
  ([6981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part010 : ℚ :=
  (302628645175 : ℚ) / 138803553493106688

def SurrogateDiagonalTailChunk000Sub000Block168Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6981
    = surrogateDiagTailX0RatChunk000Sub000Block168Part010

theorem surrogateDiagonalTailChunk000Sub000Block168Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part010] using hcert

def TailChunk000Sub000Block168Part011SupportExplicit : Finset ℕ :=
  ([6982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part011 : ℚ :=
  (304677025 : ℚ) / 148384506977202

def SurrogateDiagonalTailChunk000Sub000Block168Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6982
    = surrogateDiagTailX0RatChunk000Sub000Block168Part011

theorem surrogateDiagonalTailChunk000Sub000Block168Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part011] using hcert

def TailChunk000Sub000Block168Part012SupportExplicit : Finset ℕ :=
  ([6983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part012 : ℚ :=
  (761910765625 : ℚ) / 1485546482892211122

def SurrogateDiagonalTailChunk000Sub000Block168Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6983
    = surrogateDiagTailX0RatChunk000Sub000Block168Part012

theorem surrogateDiagonalTailChunk000Sub000Block168Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part012] using hcert

def TailChunk000Sub000Block168Part013SupportExplicit : Finset ℕ :=
  ([6985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part013 : ℚ :=
  (83141297 : ℚ) / 65854115389440

def SurrogateDiagonalTailChunk000Sub000Block168Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6985
    = surrogateDiagTailX0RatChunk000Sub000Block168Part013

theorem surrogateDiagonalTailChunk000Sub000Block168Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part013] using hcert

def TailChunk000Sub000Block168Part014SupportExplicit : Finset ℕ :=
  ([6986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part014 : ℚ :=
  (77721650125 : ℚ) / 22146582676609152

def SurrogateDiagonalTailChunk000Sub000Block168Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6986
    = surrogateDiagTailX0RatChunk000Sub000Block168Part014

theorem surrogateDiagonalTailChunk000Sub000Block168Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part014] using hcert

def TailChunk000Sub000Block168Part015SupportExplicit : Finset ℕ :=
  ([6987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part015 : ℚ :=
  (522812583525 : ℚ) / 298993089601601536

def SurrogateDiagonalTailChunk000Sub000Block168Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6987
    = surrogateDiagTailX0RatChunk000Sub000Block168Part015

theorem surrogateDiagonalTailChunk000Sub000Block168Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part015] using hcert

def TailChunk000Sub000Block168Part016SupportExplicit : Finset ℕ :=
  ([6989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part016 : ℚ :=
  (3226236761 : ℚ) / 5665802629939200

def SurrogateDiagonalTailChunk000Sub000Block168Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6989
    = surrogateDiagTailX0RatChunk000Sub000Block168Part016

theorem surrogateDiagonalTailChunk000Sub000Block168Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part016] using hcert

def TailChunk000Sub000Block168Part017SupportExplicit : Finset ℕ :=
  ([6990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part017 : ℚ :=
  (500452321525 : ℚ) / 29671448377294848

def SurrogateDiagonalTailChunk000Sub000Block168Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6990
    = surrogateDiagTailX0RatChunk000Sub000Block168Part017

theorem surrogateDiagonalTailChunk000Sub000Block168Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part017] using hcert

def TailChunk000Sub000Block168Part018SupportExplicit : Finset ℕ :=
  ([6991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part018 : ℚ :=
  (1221852025 : ℚ) / 2387786833884402

def SurrogateDiagonalTailChunk000Sub000Block168Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6991
    = surrogateDiagTailX0RatChunk000Sub000Block168Part018

theorem surrogateDiagonalTailChunk000Sub000Block168Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part018] using hcert

def TailChunk000Sub000Block168Part019SupportExplicit : Finset ℕ :=
  ([6994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part019 : ℚ :=
  (1373109880375 : ℚ) / 267479818102407168

def SurrogateDiagonalTailChunk000Sub000Block168Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6994
    = surrogateDiagTailX0RatChunk000Sub000Block168Part019

theorem surrogateDiagonalTailChunk000Sub000Block168Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part019] using hcert

def TailChunk000Sub000Block168Part020SupportExplicit : Finset ℕ :=
  ([6995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part020 : ℚ :=
  (2200296785425 : ℚ) / 2445093717897627648

def SurrogateDiagonalTailChunk000Sub000Block168Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6995
    = surrogateDiagTailX0RatChunk000Sub000Block168Part020

theorem surrogateDiagonalTailChunk000Sub000Block168Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part020] using hcert

def TailChunk000Sub000Block168Part021SupportExplicit : Finset ℕ :=
  ([6997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part021 : ℚ :=
  (764968890625 : ℚ) / 1497497378467936032

def SurrogateDiagonalTailChunk000Sub000Block168Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6997
    = surrogateDiagTailX0RatChunk000Sub000Block168Part021

theorem surrogateDiagonalTailChunk000Sub000Block168Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part021] using hcert

def TailChunk000Sub000Block168Part022SupportExplicit : Finset ℕ :=
  ([6998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part022 : ℚ :=
  (1530069049975 : ℚ) / 374374344616984008

def SurrogateDiagonalTailChunk000Sub000Block168Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6998
    = surrogateDiagTailX0RatChunk000Sub000Block168Part022

theorem surrogateDiagonalTailChunk000Sub000Block168Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part022] using hcert

def TailChunk000Sub000Block168Part023SupportExplicit : Finset ℕ :=
  ([6999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part023 : ℚ :=
  (850170895175 : ℚ) / 591603902604616704

def SurrogateDiagonalTailChunk000Sub000Block168Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6999
    = surrogateDiagTailX0RatChunk000Sub000Block168Part023

theorem surrogateDiagonalTailChunk000Sub000Block168Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part023] using hcert

def TailChunk000Sub000Block168Part024SupportExplicit : Finset ℕ :=
  ([7001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part024 : ℚ :=
  (49014001 : ℚ) / 96059208000000

def SurrogateDiagonalTailChunk000Sub000Block168Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7001
    = surrogateDiagTailX0RatChunk000Sub000Block168Part024

theorem surrogateDiagonalTailChunk000Sub000Block168Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block168HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block168Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block168Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block168Part000
    + surrogateDiagTailX0RatChunk000Sub000Block168Part001
    + surrogateDiagTailX0RatChunk000Sub000Block168Part002
    + surrogateDiagTailX0RatChunk000Sub000Block168Part003
    + surrogateDiagTailX0RatChunk000Sub000Block168Part004
    + surrogateDiagTailX0RatChunk000Sub000Block168Part005
    + surrogateDiagTailX0RatChunk000Sub000Block168Part006
    + surrogateDiagTailX0RatChunk000Sub000Block168Part007
    + surrogateDiagTailX0RatChunk000Sub000Block168Part008
    + surrogateDiagTailX0RatChunk000Sub000Block168Part009

def surrogateDiagonalTailChunk000Sub000Block168MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block168Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block168Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block168Part010
    + surrogateDiagTailX0RatChunk000Sub000Block168Part011
    + surrogateDiagTailX0RatChunk000Sub000Block168Part012
    + surrogateDiagTailX0RatChunk000Sub000Block168Part013
    + surrogateDiagTailX0RatChunk000Sub000Block168Part014
    + surrogateDiagTailX0RatChunk000Sub000Block168Part015
    + surrogateDiagTailX0RatChunk000Sub000Block168Part016
    + surrogateDiagTailX0RatChunk000Sub000Block168Part017
    + surrogateDiagTailX0RatChunk000Sub000Block168Part018
    + surrogateDiagTailX0RatChunk000Sub000Block168Part019

def surrogateDiagonalTailChunk000Sub000Block168TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block168Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block168Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block168Part020
    + surrogateDiagTailX0RatChunk000Sub000Block168Part021
    + surrogateDiagTailX0RatChunk000Sub000Block168Part022
    + surrogateDiagTailX0RatChunk000Sub000Block168Part023
    + surrogateDiagTailX0RatChunk000Sub000Block168Part024

def surrogateDiagonalTailChunk000Sub000Block168Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block168HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block168MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block168TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block168 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block168Part000
    + surrogateDiagTailX0RatChunk000Sub000Block168Part001
    + surrogateDiagTailX0RatChunk000Sub000Block168Part002
    + surrogateDiagTailX0RatChunk000Sub000Block168Part003
    + surrogateDiagTailX0RatChunk000Sub000Block168Part004
    + surrogateDiagTailX0RatChunk000Sub000Block168Part005
    + surrogateDiagTailX0RatChunk000Sub000Block168Part006
    + surrogateDiagTailX0RatChunk000Sub000Block168Part007
    + surrogateDiagTailX0RatChunk000Sub000Block168Part008
    + surrogateDiagTailX0RatChunk000Sub000Block168Part009
    + surrogateDiagTailX0RatChunk000Sub000Block168Part010
    + surrogateDiagTailX0RatChunk000Sub000Block168Part011
    + surrogateDiagTailX0RatChunk000Sub000Block168Part012
    + surrogateDiagTailX0RatChunk000Sub000Block168Part013
    + surrogateDiagTailX0RatChunk000Sub000Block168Part014
    + surrogateDiagTailX0RatChunk000Sub000Block168Part015
    + surrogateDiagTailX0RatChunk000Sub000Block168Part016
    + surrogateDiagTailX0RatChunk000Sub000Block168Part017
    + surrogateDiagTailX0RatChunk000Sub000Block168Part018
    + surrogateDiagTailX0RatChunk000Sub000Block168Part019
    + surrogateDiagTailX0RatChunk000Sub000Block168Part020
    + surrogateDiagTailX0RatChunk000Sub000Block168Part021
    + surrogateDiagTailX0RatChunk000Sub000Block168Part022
    + surrogateDiagTailX0RatChunk000Sub000Block168Part023
    + surrogateDiagTailX0RatChunk000Sub000Block168Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block168_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block168Head + surrogateDiagTailX0RatChunk000Sub000Block168Mid + surrogateDiagTailX0RatChunk000Sub000Block168Tail =
      surrogateDiagTailX0RatChunk000Sub000Block168 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block168Head surrogateDiagTailX0RatChunk000Sub000Block168Mid surrogateDiagTailX0RatChunk000Sub000Block168Tail surrogateDiagTailX0RatChunk000Sub000Block168
  ring

def SurrogateDiagonalTailChunk000Sub000Block168HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block168HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block168Head

def SurrogateDiagonalTailChunk000Sub000Block168MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block168MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block168Mid

def SurrogateDiagonalTailChunk000Sub000Block168TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block168TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block168Tail

theorem surrogateDiagonalTailChunk000Sub000Block168_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block168HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block168MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block168TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block168Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block168 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block168HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block168MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block168TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block168Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block168_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
