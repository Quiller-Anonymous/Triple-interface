import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [83,84). -/

/- Block 083 covers tail-support indices [2075,2100) and q from 3458 to 3498. -/

def TailChunk000Sub000Block083Part000SupportExplicit : Finset ℕ :=
  ([3458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part000 : ℚ :=
  (207452717375 : ℚ) / 3527092661796864

def SurrogateDiagonalTailChunk000Sub000Block083Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3458
    = surrogateDiagTailX0RatChunk000Sub000Block083Part000

theorem surrogateDiagonalTailChunk000Sub000Block083Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part000] using hcert

def TailChunk000Sub000Block083Part001SupportExplicit : Finset ℕ :=
  ([3459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part001 : ℚ :=
  (581332316425 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block083Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3459
    = surrogateDiagTailX0RatChunk000Sub000Block083Part001

theorem surrogateDiagonalTailChunk000Sub000Block083Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part001] using hcert

def TailChunk000Sub000Block083Part002SupportExplicit : Finset ℕ :=
  ([3461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part002 : ℚ :=
  (299463025 : ℚ) / 143347870401312

def SurrogateDiagonalTailChunk000Sub000Block083Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3461
    = surrogateDiagTailX0RatChunk000Sub000Block083Part002

theorem surrogateDiagonalTailChunk000Sub000Block083Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part002] using hcert

def TailChunk000Sub000Block083Part003SupportExplicit : Finset ℕ :=
  ([3462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part003 : ℚ :=
  (194725 : ℚ) / 2293235712

def SurrogateDiagonalTailChunk000Sub000Block083Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3462
    = surrogateDiagTailX0RatChunk000Sub000Block083Part003

theorem surrogateDiagonalTailChunk000Sub000Block083Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part003] using hcert

def TailChunk000Sub000Block083Part004SupportExplicit : Finset ℕ :=
  ([3463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part004 : ℚ :=
  (187380765625 : ℚ) / 89799748781694642

def SurrogateDiagonalTailChunk000Sub000Block083Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3463
    = surrogateDiagTailX0RatChunk000Sub000Block083Part004

theorem surrogateDiagonalTailChunk000Sub000Block083Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part004] using hcert

def TailChunk000Sub000Block083Part005SupportExplicit : Finset ℕ :=
  ([3466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part005 : ℚ :=
  (187630480275 : ℚ) / 7500619849818496

def SurrogateDiagonalTailChunk000Sub000Block083Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3466
    = surrogateDiagTailX0RatChunk000Sub000Block083Part005

theorem surrogateDiagonalTailChunk000Sub000Block083Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part005] using hcert

def TailChunk000Sub000Block083Part006SupportExplicit : Finset ℕ :=
  ([3467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part006 : ℚ :=
  (187813890625 : ℚ) / 90215487664845042

def SurrogateDiagonalTailChunk000Sub000Block083Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3467
    = surrogateDiagTailX0RatChunk000Sub000Block083Part006

theorem surrogateDiagonalTailChunk000Sub000Block083Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part006] using hcert

def TailChunk000Sub000Block083Part007SupportExplicit : Finset ℕ :=
  ([3469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part007 : ℚ :=
  (188030640625 : ℚ) / 90423897598647072

def SurrogateDiagonalTailChunk000Sub000Block083Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3469
    = surrogateDiagTailX0RatChunk000Sub000Block083Part007

theorem surrogateDiagonalTailChunk000Sub000Block083Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part007] using hcert

def TailChunk000Sub000Block083Part008SupportExplicit : Finset ℕ :=
  ([3470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part008 : ℚ :=
  (225136143125 : ℚ) / 4587131852841984

def SurrogateDiagonalTailChunk000Sub000Block083Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3470
    = surrogateDiagTailX0RatChunk000Sub000Block083Part008

theorem surrogateDiagonalTailChunk000Sub000Block083Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part008] using hcert

def TailChunk000Sub000Block083Part009SupportExplicit : Finset ℕ :=
  ([3471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part009 : ℚ :=
  (547181433475 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block083Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3471
    = surrogateDiagTailX0RatChunk000Sub000Block083Part009

theorem surrogateDiagonalTailChunk000Sub000Block083Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part009] using hcert

def TailChunk000Sub000Block083Part010SupportExplicit : Finset ℕ :=
  ([3473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part010 : ℚ :=
  (14118782323 : ℚ) / 2965395460500000

def SurrogateDiagonalTailChunk000Sub000Block083Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3473
    = surrogateDiagTailX0RatChunk000Sub000Block083Part010

theorem surrogateDiagonalTailChunk000Sub000Block083Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part010] using hcert

def TailChunk000Sub000Block083Part011SupportExplicit : Finset ℕ :=
  ([3477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part011 : ℚ :=
  (6196497203 : ℚ) / 435443538493440

def SurrogateDiagonalTailChunk000Sub000Block083Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3477
    = surrogateDiagTailX0RatChunk000Sub000Block083Part011

theorem surrogateDiagonalTailChunk000Sub000Block083Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part011] using hcert

def TailChunk000Sub000Block083Part012SupportExplicit : Finset ℕ :=
  ([3478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part012 : ℚ :=
  (538906471375 : ℚ) / 18804777045608448

def SurrogateDiagonalTailChunk000Sub000Block083Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3478
    = surrogateDiagTailX0RatChunk000Sub000Block083Part012

theorem surrogateDiagonalTailChunk000Sub000Block083Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part012] using hcert

def TailChunk000Sub000Block083Part013SupportExplicit : Finset ℕ :=
  ([3482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part013 : ℚ :=
  (2524890473 : ℚ) / 101868833692800

def SurrogateDiagonalTailChunk000Sub000Block083Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3482
    = surrogateDiagTailX0RatChunk000Sub000Block083Part013

theorem surrogateDiagonalTailChunk000Sub000Block083Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part013] using hcert

def TailChunk000Sub000Block083Part014SupportExplicit : Finset ℕ :=
  ([3485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part014 : ℚ :=
  (6289643893 : ℚ) / 1073956572364800

def SurrogateDiagonalTailChunk000Sub000Block083Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3485
    = surrogateDiagTailX0RatChunk000Sub000Block083Part014

theorem surrogateDiagonalTailChunk000Sub000Block083Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part014] using hcert

def TailChunk000Sub000Block083Part015SupportExplicit : Finset ℕ :=
  ([3486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part015 : ℚ :=
  (5314825 : ℚ) / 39063320064

def SurrogateDiagonalTailChunk000Sub000Block083Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3486
    = surrogateDiagTailX0RatChunk000Sub000Block083Part015

theorem surrogateDiagonalTailChunk000Sub000Block083Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part015] using hcert

def TailChunk000Sub000Block083Part016SupportExplicit : Finset ℕ :=
  ([3487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part016 : ℚ :=
  (1153517269 : ℚ) / 398928599205888

def SurrogateDiagonalTailChunk000Sub000Block083Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3487
    = surrogateDiagTailX0RatChunk000Sub000Block083Part016

theorem surrogateDiagonalTailChunk000Sub000Block083Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part016] using hcert

def TailChunk000Sub000Block083Part017SupportExplicit : Finset ℕ :=
  ([3489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part017 : ℚ :=
  (675814145875 : ℚ) / 72940939652316288

def SurrogateDiagonalTailChunk000Sub000Block083Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3489
    = surrogateDiagTailX0RatChunk000Sub000Block083Part017

theorem surrogateDiagonalTailChunk000Sub000Block083Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part017] using hcert

def TailChunk000Sub000Block083Part018SupportExplicit : Finset ℕ :=
  ([3490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part018 : ℚ :=
  (74651064725 : ℚ) / 1564705285521408

def SurrogateDiagonalTailChunk000Sub000Block083Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3490
    = surrogateDiagTailX0RatChunk000Sub000Block083Part018

theorem surrogateDiagonalTailChunk000Sub000Block083Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part018] using hcert

def TailChunk000Sub000Block083Part019SupportExplicit : Finset ℕ :=
  ([3491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part019 : ℚ :=
  (304677025 : ℚ) / 148384506977202

def SurrogateDiagonalTailChunk000Sub000Block083Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3491
    = surrogateDiagTailX0RatChunk000Sub000Block083Part019

theorem surrogateDiagonalTailChunk000Sub000Block083Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part019] using hcert

def TailChunk000Sub000Block083Part020SupportExplicit : Finset ℕ :=
  ([3493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part020 : ℚ :=
  (77721650125 : ℚ) / 22146582676609152

def SurrogateDiagonalTailChunk000Sub000Block083Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3493
    = surrogateDiagTailX0RatChunk000Sub000Block083Part020

theorem surrogateDiagonalTailChunk000Sub000Block083Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part020] using hcert

def TailChunk000Sub000Block083Part021SupportExplicit : Finset ℕ :=
  ([3494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part021 : ℚ :=
  (63558087425 : ℚ) / 2582030136726792

def SurrogateDiagonalTailChunk000Sub000Block083Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3494
    = surrogateDiagTailX0RatChunk000Sub000Block083Part021

theorem surrogateDiagonalTailChunk000Sub000Block083Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part021] using hcert

def TailChunk000Sub000Block083Part022SupportExplicit : Finset ℕ :=
  ([3495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part022 : ℚ :=
  (500452321525 : ℚ) / 29671448377294848

def SurrogateDiagonalTailChunk000Sub000Block083Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3495
    = surrogateDiagTailX0RatChunk000Sub000Block083Part022

theorem surrogateDiagonalTailChunk000Sub000Block083Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part022] using hcert

def TailChunk000Sub000Block083Part023SupportExplicit : Finset ℕ :=
  ([3497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part023 : ℚ :=
  (1373109880375 : ℚ) / 267479818102407168

def SurrogateDiagonalTailChunk000Sub000Block083Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3497
    = surrogateDiagTailX0RatChunk000Sub000Block083Part023

theorem surrogateDiagonalTailChunk000Sub000Block083Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part023] using hcert

def TailChunk000Sub000Block083Part024SupportExplicit : Finset ℕ :=
  ([3498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block083Part024 : ℚ :=
  (1045056889 : ℚ) / 9000711782400

def SurrogateDiagonalTailChunk000Sub000Block083Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3498
    = surrogateDiagTailX0RatChunk000Sub000Block083Part024

theorem surrogateDiagonalTailChunk000Sub000Block083Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block083Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block083Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block083Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block083Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block083Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block083Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block083HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block083Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block083Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block083Part000
    + surrogateDiagTailX0RatChunk000Sub000Block083Part001
    + surrogateDiagTailX0RatChunk000Sub000Block083Part002
    + surrogateDiagTailX0RatChunk000Sub000Block083Part003
    + surrogateDiagTailX0RatChunk000Sub000Block083Part004
    + surrogateDiagTailX0RatChunk000Sub000Block083Part005
    + surrogateDiagTailX0RatChunk000Sub000Block083Part006
    + surrogateDiagTailX0RatChunk000Sub000Block083Part007
    + surrogateDiagTailX0RatChunk000Sub000Block083Part008
    + surrogateDiagTailX0RatChunk000Sub000Block083Part009

def surrogateDiagonalTailChunk000Sub000Block083MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block083Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block083Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block083Part010
    + surrogateDiagTailX0RatChunk000Sub000Block083Part011
    + surrogateDiagTailX0RatChunk000Sub000Block083Part012
    + surrogateDiagTailX0RatChunk000Sub000Block083Part013
    + surrogateDiagTailX0RatChunk000Sub000Block083Part014
    + surrogateDiagTailX0RatChunk000Sub000Block083Part015
    + surrogateDiagTailX0RatChunk000Sub000Block083Part016
    + surrogateDiagTailX0RatChunk000Sub000Block083Part017
    + surrogateDiagTailX0RatChunk000Sub000Block083Part018
    + surrogateDiagTailX0RatChunk000Sub000Block083Part019

def surrogateDiagonalTailChunk000Sub000Block083TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block083Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block083Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block083Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block083Part020
    + surrogateDiagTailX0RatChunk000Sub000Block083Part021
    + surrogateDiagTailX0RatChunk000Sub000Block083Part022
    + surrogateDiagTailX0RatChunk000Sub000Block083Part023
    + surrogateDiagTailX0RatChunk000Sub000Block083Part024

def surrogateDiagonalTailChunk000Sub000Block083Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block083HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block083MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block083TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block083 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block083Part000
    + surrogateDiagTailX0RatChunk000Sub000Block083Part001
    + surrogateDiagTailX0RatChunk000Sub000Block083Part002
    + surrogateDiagTailX0RatChunk000Sub000Block083Part003
    + surrogateDiagTailX0RatChunk000Sub000Block083Part004
    + surrogateDiagTailX0RatChunk000Sub000Block083Part005
    + surrogateDiagTailX0RatChunk000Sub000Block083Part006
    + surrogateDiagTailX0RatChunk000Sub000Block083Part007
    + surrogateDiagTailX0RatChunk000Sub000Block083Part008
    + surrogateDiagTailX0RatChunk000Sub000Block083Part009
    + surrogateDiagTailX0RatChunk000Sub000Block083Part010
    + surrogateDiagTailX0RatChunk000Sub000Block083Part011
    + surrogateDiagTailX0RatChunk000Sub000Block083Part012
    + surrogateDiagTailX0RatChunk000Sub000Block083Part013
    + surrogateDiagTailX0RatChunk000Sub000Block083Part014
    + surrogateDiagTailX0RatChunk000Sub000Block083Part015
    + surrogateDiagTailX0RatChunk000Sub000Block083Part016
    + surrogateDiagTailX0RatChunk000Sub000Block083Part017
    + surrogateDiagTailX0RatChunk000Sub000Block083Part018
    + surrogateDiagTailX0RatChunk000Sub000Block083Part019
    + surrogateDiagTailX0RatChunk000Sub000Block083Part020
    + surrogateDiagTailX0RatChunk000Sub000Block083Part021
    + surrogateDiagTailX0RatChunk000Sub000Block083Part022
    + surrogateDiagTailX0RatChunk000Sub000Block083Part023
    + surrogateDiagTailX0RatChunk000Sub000Block083Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block083_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block083Head + surrogateDiagTailX0RatChunk000Sub000Block083Mid + surrogateDiagTailX0RatChunk000Sub000Block083Tail =
      surrogateDiagTailX0RatChunk000Sub000Block083 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block083Head surrogateDiagTailX0RatChunk000Sub000Block083Mid surrogateDiagTailX0RatChunk000Sub000Block083Tail surrogateDiagTailX0RatChunk000Sub000Block083
  ring

def SurrogateDiagonalTailChunk000Sub000Block083HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block083HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block083Head

def SurrogateDiagonalTailChunk000Sub000Block083MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block083MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block083Mid

def SurrogateDiagonalTailChunk000Sub000Block083TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block083TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block083Tail

theorem surrogateDiagonalTailChunk000Sub000Block083_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block083HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block083MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block083TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block083Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block083 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block083HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block083MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block083TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block083Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block083_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
