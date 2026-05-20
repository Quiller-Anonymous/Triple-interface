import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [152,153). -/

/- Block 152 covers tail-support indices [3800,3825) and q from 6301 to 6339. -/

def TailChunk000Sub000Block152Part000SupportExplicit : Finset ℕ :=
  ([6301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part000 : ℚ :=
  (39702601 : ℚ) / 63024446368800

def SurrogateDiagonalTailChunk000Sub000Block152Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6301
    = surrogateDiagTailX0RatChunk000Sub000Block152Part000

theorem surrogateDiagonalTailChunk000Sub000Block152Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part000] using hcert

def TailChunk000Sub000Block152Part001SupportExplicit : Finset ℕ :=
  ([6302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part001 : ℚ :=
  (291620625775 : ℚ) / 50097173593792512

def SurrogateDiagonalTailChunk000Sub000Block152Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6302
    = surrogateDiagTailX0RatChunk000Sub000Block152Part001

theorem surrogateDiagonalTailChunk000Sub000Block152Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part001] using hcert

def TailChunk000Sub000Block152Part002SupportExplicit : Finset ℕ :=
  ([6303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part002 : ℚ :=
  (1466307943 : ℚ) / 521388256800000

def SurrogateDiagonalTailChunk000Sub000Block152Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6303
    = surrogateDiagTailX0RatChunk000Sub000Block152Part002

theorem surrogateDiagonalTailChunk000Sub000Block152Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part002] using hcert

def TailChunk000Sub000Block152Part003SupportExplicit : Finset ℕ :=
  ([6305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part003 : ℚ :=
  (1705144479625 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub000Block152Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6305
    = surrogateDiagTailX0RatChunk000Sub000Block152Part003

theorem surrogateDiagonalTailChunk000Sub000Block152Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part003] using hcert

def TailChunk000Sub000Block152Part004SupportExplicit : Finset ℕ :=
  ([6306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part004 : ℚ :=
  (6069848789 : ℚ) / 389039792400000

def SurrogateDiagonalTailChunk000Sub000Block152Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6306
    = surrogateDiagTailX0RatChunk000Sub000Block152Part004

theorem surrogateDiagonalTailChunk000Sub000Block152Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part004] using hcert

def TailChunk000Sub000Block152Part005SupportExplicit : Finset ℕ :=
  ([6307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part005 : ℚ :=
  (1895430372625 : ℚ) / 1552834479205122048

def SurrogateDiagonalTailChunk000Sub000Block152Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6307
    = surrogateDiagTailX0RatChunk000Sub000Block152Part005

theorem surrogateDiagonalTailChunk000Sub000Block152Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part005] using hcert

def TailChunk000Sub000Block152Part006SupportExplicit : Finset ℕ :=
  ([6310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part006 : ℚ :=
  (37762204807 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block152Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6310
    = surrogateDiagTailX0RatChunk000Sub000Block152Part006

theorem surrogateDiagonalTailChunk000Sub000Block152Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part006] using hcert

def TailChunk000Sub000Block152Part007SupportExplicit : Finset ℕ :=
  ([6311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part007 : ℚ :=
  (995718025 : ℚ) / 1585638883573842

def SurrogateDiagonalTailChunk000Sub000Block152Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6311
    = surrogateDiagTailX0RatChunk000Sub000Block152Part007

theorem surrogateDiagonalTailChunk000Sub000Block152Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part007] using hcert

def TailChunk000Sub000Block152Part008SupportExplicit : Finset ℕ :=
  ([6313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part008 : ℚ :=
  (8478941775 : ℚ) / 595403034626072768

def SurrogateDiagonalTailChunk000Sub000Block152Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6313
    = surrogateDiagTailX0RatChunk000Sub000Block152Part008

theorem surrogateDiagonalTailChunk000Sub000Block152Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part008] using hcert

def TailChunk000Sub000Block152Part009SupportExplicit : Finset ℕ :=
  ([6314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part009 : ℚ :=
  (21824421367 : ℚ) / 3318423552000000

def SurrogateDiagonalTailChunk000Sub000Block152Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6314
    = surrogateDiagTailX0RatChunk000Sub000Block152Part009

theorem surrogateDiagonalTailChunk000Sub000Block152Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part009] using hcert

def TailChunk000Sub000Block152Part010SupportExplicit : Finset ℕ :=
  ([6315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part010 : ℚ :=
  (442774681 : ℚ) / 236075109580800

def SurrogateDiagonalTailChunk000Sub000Block152Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6315
    = surrogateDiagTailX0RatChunk000Sub000Block152Part010

theorem surrogateDiagonalTailChunk000Sub000Block152Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part010] using hcert

def TailChunk000Sub000Block152Part011SupportExplicit : Finset ℕ :=
  ([6317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block152Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6317
    = surrogateDiagTailX0RatChunk000Sub000Block152Part011

theorem surrogateDiagonalTailChunk000Sub000Block152Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part011] using hcert

def TailChunk000Sub000Block152Part012SupportExplicit : Finset ℕ :=
  ([6319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part012 : ℚ :=
  (1960888759 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub000Block152Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6319
    = surrogateDiagTailX0RatChunk000Sub000Block152Part012

theorem surrogateDiagonalTailChunk000Sub000Block152Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part012] using hcert

def TailChunk000Sub000Block152Part013SupportExplicit : Finset ℕ :=
  ([6322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part013 : ℚ :=
  (76637410475 : ℚ) / 26137498398068736

def SurrogateDiagonalTailChunk000Sub000Block152Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6322
    = surrogateDiagTailX0RatChunk000Sub000Block152Part013

theorem surrogateDiagonalTailChunk000Sub000Block152Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part013] using hcert

def TailChunk000Sub000Block152Part014SupportExplicit : Finset ℕ :=
  ([6323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block152Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6323
    = surrogateDiagTailX0RatChunk000Sub000Block152Part014

theorem surrogateDiagonalTailChunk000Sub000Block152Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part014] using hcert

def TailChunk000Sub000Block152Part015SupportExplicit : Finset ℕ :=
  ([6326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part015 : ℚ :=
  (156321390625 : ℚ) / 62490547537595442

def SurrogateDiagonalTailChunk000Sub000Block152Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6326
    = surrogateDiagTailX0RatChunk000Sub000Block152Part015

theorem surrogateDiagonalTailChunk000Sub000Block152Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part015] using hcert

def TailChunk000Sub000Block152Part016SupportExplicit : Finset ℕ :=
  ([6329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block152Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6329
    = surrogateDiagTailX0RatChunk000Sub000Block152Part016

theorem surrogateDiagonalTailChunk000Sub000Block152Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part016] using hcert

def TailChunk000Sub000Block152Part017SupportExplicit : Finset ℕ :=
  ([6330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part017 : ℚ :=
  (655190887 : ℚ) / 22132041523200

def SurrogateDiagonalTailChunk000Sub000Block152Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6330
    = surrogateDiagTailX0RatChunk000Sub000Block152Part017

theorem surrogateDiagonalTailChunk000Sub000Block152Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part017] using hcert

def TailChunk000Sub000Block152Part018SupportExplicit : Finset ℕ :=
  ([6331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part018 : ℚ :=
  (2262794125525 : ℚ) / 2892656869256153088

def SurrogateDiagonalTailChunk000Sub000Block152Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6331
    = surrogateDiagTailX0RatChunk000Sub000Block152Part018

theorem surrogateDiagonalTailChunk000Sub000Block152Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part018] using hcert

def TailChunk000Sub000Block152Part019SupportExplicit : Finset ℕ :=
  ([6333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part019 : ℚ :=
  (6680649 : ℚ) / 3171391105600

def SurrogateDiagonalTailChunk000Sub000Block152Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6333
    = surrogateDiagTailX0RatChunk000Sub000Block152Part019

theorem surrogateDiagonalTailChunk000Sub000Block152Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part019] using hcert

def TailChunk000Sub000Block152Part020SupportExplicit : Finset ℕ :=
  ([6334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part020 : ℚ :=
  (1253485377775 : ℚ) / 251229423050282568

def SurrogateDiagonalTailChunk000Sub000Block152Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6334
    = surrogateDiagTailX0RatChunk000Sub000Block152Part020

theorem surrogateDiagonalTailChunk000Sub000Block152Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part020] using hcert

def TailChunk000Sub000Block152Part021SupportExplicit : Finset ℕ :=
  ([6335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part021 : ℚ :=
  (63733582447 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block152Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6335
    = surrogateDiagTailX0RatChunk000Sub000Block152Part021

theorem surrogateDiagonalTailChunk000Sub000Block152Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part021] using hcert

def TailChunk000Sub000Block152Part022SupportExplicit : Finset ℕ :=
  ([6337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part022 : ℚ :=
  (627462015625 : ℚ) / 1007459373366116352

def SurrogateDiagonalTailChunk000Sub000Block152Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6337
    = surrogateDiagTailX0RatChunk000Sub000Block152Part022

theorem surrogateDiagonalTailChunk000Sub000Block152Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part022] using hcert

def TailChunk000Sub000Block152Part023SupportExplicit : Finset ℕ :=
  ([6338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part023 : ℚ :=
  (1255069060975 : ℚ) / 251864843341529088

def SurrogateDiagonalTailChunk000Sub000Block152Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6338
    = surrogateDiagTailX0RatChunk000Sub000Block152Part023

theorem surrogateDiagonalTailChunk000Sub000Block152Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part023] using hcert

def TailChunk000Sub000Block152Part024SupportExplicit : Finset ℕ :=
  ([6339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block152Part024 : ℚ :=
  (697383955925 : ℚ) / 398008641329823744

def SurrogateDiagonalTailChunk000Sub000Block152Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6339
    = surrogateDiagTailX0RatChunk000Sub000Block152Part024

theorem surrogateDiagonalTailChunk000Sub000Block152Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block152Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block152Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block152Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block152Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block152Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block152Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block152HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block152Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block152Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block152Part000
    + surrogateDiagTailX0RatChunk000Sub000Block152Part001
    + surrogateDiagTailX0RatChunk000Sub000Block152Part002
    + surrogateDiagTailX0RatChunk000Sub000Block152Part003
    + surrogateDiagTailX0RatChunk000Sub000Block152Part004
    + surrogateDiagTailX0RatChunk000Sub000Block152Part005
    + surrogateDiagTailX0RatChunk000Sub000Block152Part006
    + surrogateDiagTailX0RatChunk000Sub000Block152Part007
    + surrogateDiagTailX0RatChunk000Sub000Block152Part008
    + surrogateDiagTailX0RatChunk000Sub000Block152Part009

def surrogateDiagonalTailChunk000Sub000Block152MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block152Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block152Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block152Part010
    + surrogateDiagTailX0RatChunk000Sub000Block152Part011
    + surrogateDiagTailX0RatChunk000Sub000Block152Part012
    + surrogateDiagTailX0RatChunk000Sub000Block152Part013
    + surrogateDiagTailX0RatChunk000Sub000Block152Part014
    + surrogateDiagTailX0RatChunk000Sub000Block152Part015
    + surrogateDiagTailX0RatChunk000Sub000Block152Part016
    + surrogateDiagTailX0RatChunk000Sub000Block152Part017
    + surrogateDiagTailX0RatChunk000Sub000Block152Part018
    + surrogateDiagTailX0RatChunk000Sub000Block152Part019

def surrogateDiagonalTailChunk000Sub000Block152TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block152Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block152Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block152Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block152Part020
    + surrogateDiagTailX0RatChunk000Sub000Block152Part021
    + surrogateDiagTailX0RatChunk000Sub000Block152Part022
    + surrogateDiagTailX0RatChunk000Sub000Block152Part023
    + surrogateDiagTailX0RatChunk000Sub000Block152Part024

def surrogateDiagonalTailChunk000Sub000Block152Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block152HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block152MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block152TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block152 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block152Part000
    + surrogateDiagTailX0RatChunk000Sub000Block152Part001
    + surrogateDiagTailX0RatChunk000Sub000Block152Part002
    + surrogateDiagTailX0RatChunk000Sub000Block152Part003
    + surrogateDiagTailX0RatChunk000Sub000Block152Part004
    + surrogateDiagTailX0RatChunk000Sub000Block152Part005
    + surrogateDiagTailX0RatChunk000Sub000Block152Part006
    + surrogateDiagTailX0RatChunk000Sub000Block152Part007
    + surrogateDiagTailX0RatChunk000Sub000Block152Part008
    + surrogateDiagTailX0RatChunk000Sub000Block152Part009
    + surrogateDiagTailX0RatChunk000Sub000Block152Part010
    + surrogateDiagTailX0RatChunk000Sub000Block152Part011
    + surrogateDiagTailX0RatChunk000Sub000Block152Part012
    + surrogateDiagTailX0RatChunk000Sub000Block152Part013
    + surrogateDiagTailX0RatChunk000Sub000Block152Part014
    + surrogateDiagTailX0RatChunk000Sub000Block152Part015
    + surrogateDiagTailX0RatChunk000Sub000Block152Part016
    + surrogateDiagTailX0RatChunk000Sub000Block152Part017
    + surrogateDiagTailX0RatChunk000Sub000Block152Part018
    + surrogateDiagTailX0RatChunk000Sub000Block152Part019
    + surrogateDiagTailX0RatChunk000Sub000Block152Part020
    + surrogateDiagTailX0RatChunk000Sub000Block152Part021
    + surrogateDiagTailX0RatChunk000Sub000Block152Part022
    + surrogateDiagTailX0RatChunk000Sub000Block152Part023
    + surrogateDiagTailX0RatChunk000Sub000Block152Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block152_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block152Head + surrogateDiagTailX0RatChunk000Sub000Block152Mid + surrogateDiagTailX0RatChunk000Sub000Block152Tail =
      surrogateDiagTailX0RatChunk000Sub000Block152 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block152Head surrogateDiagTailX0RatChunk000Sub000Block152Mid surrogateDiagTailX0RatChunk000Sub000Block152Tail surrogateDiagTailX0RatChunk000Sub000Block152
  ring

def SurrogateDiagonalTailChunk000Sub000Block152HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block152HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block152Head

def SurrogateDiagonalTailChunk000Sub000Block152MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block152MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block152Mid

def SurrogateDiagonalTailChunk000Sub000Block152TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block152TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block152Tail

theorem surrogateDiagonalTailChunk000Sub000Block152_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block152HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block152MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block152TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block152Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block152 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block152HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block152MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block152TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block152Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block152_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
