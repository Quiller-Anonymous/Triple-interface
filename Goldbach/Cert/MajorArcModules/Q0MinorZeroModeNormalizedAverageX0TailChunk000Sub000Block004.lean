import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [4,5). -/

/- Block 004 covers tail-support indices [100,125) and q from 214 to 254. -/

def TailChunk000Sub000Block004Part000SupportExplicit : Finset ℕ :=
  ([214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part000 : ℚ :=
  (33322028275 : ℚ) / 315682363848

def SurrogateDiagonalTailChunk000Sub000Block004Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 214
    = surrogateDiagTailX0RatChunk000Sub000Block004Part000

theorem surrogateDiagonalTailChunk000Sub000Block004Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part000] using hcert

def TailChunk000Sub000Block004Part001SupportExplicit : Finset ℕ :=
  ([215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part001 : ℚ :=
  (5796439475 : ℚ) / 221320415232

def SurrogateDiagonalTailChunk000Sub000Block004Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 215
    = surrogateDiagTailX0RatChunk000Sub000Block004Part001

theorem surrogateDiagonalTailChunk000Sub000Block004Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part001] using hcert

def TailChunk000Sub000Block004Part002SupportExplicit : Finset ℕ :=
  ([217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part002 : ℚ :=
  (62403103 : ℚ) / 2916583200

def SurrogateDiagonalTailChunk000Sub000Block004Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 217
    = surrogateDiagTailX0RatChunk000Sub000Block004Part002

theorem surrogateDiagonalTailChunk000Sub000Block004Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part002] using hcert

def TailChunk000Sub000Block004Part003SupportExplicit : Finset ℕ :=
  ([218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part003 : ℚ :=
  (33850454125 : ℚ) / 340190264448

def SurrogateDiagonalTailChunk000Sub000Block004Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 218
    = surrogateDiagTailX0RatChunk000Sub000Block004Part003

theorem surrogateDiagonalTailChunk000Sub000Block004Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part003] using hcert

def TailChunk000Sub000Block004Part004SupportExplicit : Finset ℕ :=
  ([219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part004 : ℚ :=
  (11010322525 : ℚ) / 268792307712

def SurrogateDiagonalTailChunk000Sub000Block004Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 219
    = surrogateDiagTailX0RatChunk000Sub000Block004Part004

theorem surrogateDiagonalTailChunk000Sub000Block004Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part004] using hcert

def TailChunk000Sub000Block004Part005SupportExplicit : Finset ℕ :=
  ([221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part005 : ℚ :=
  (634058875 : ℚ) / 35396517888

def SurrogateDiagonalTailChunk000Sub000Block004Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 221
    = surrogateDiagTailX0RatChunk000Sub000Block004Part005

theorem surrogateDiagonalTailChunk000Sub000Block004Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part005] using hcert

def TailChunk000Sub000Block004Part006SupportExplicit : Finset ℕ :=
  ([222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part006 : ℚ :=
  (749275 : ℚ) / 2239488

def SurrogateDiagonalTailChunk000Sub000Block004Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 222
    = surrogateDiagTailX0RatChunk000Sub000Block004Part006

theorem surrogateDiagonalTailChunk000Sub000Block004Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part006] using hcert

def TailChunk000Sub000Block004Part007SupportExplicit : Finset ℕ :=
  ([223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part007 : ℚ :=
  (68090190025 : ℚ) / 6073496096328

def SurrogateDiagonalTailChunk000Sub000Block004Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 223
    = surrogateDiagTailX0RatChunk000Sub000Block004Part007

theorem surrogateDiagonalTailChunk000Sub000Block004Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part007] using hcert

def TailChunk000Sub000Block004Part008SupportExplicit : Finset ℕ :=
  ([226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part008 : ℚ :=
  (847542375 : ℚ) / 9368059904

def SurrogateDiagonalTailChunk000Sub000Block004Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 226
    = surrogateDiagTailX0RatChunk000Sub000Block004Part008

theorem surrogateDiagonalTailChunk000Sub000Block004Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part008] using hcert

def TailChunk000Sub000Block004Part009SupportExplicit : Finset ℕ :=
  ([227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part009 : ℚ :=
  (70554795025 : ℚ) / 6523198818888

def SurrogateDiagonalTailChunk000Sub000Block004Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 227
    = surrogateDiagTailX0RatChunk000Sub000Block004Part009

theorem surrogateDiagonalTailChunk000Sub000Block004Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part009] using hcert

def TailChunk000Sub000Block004Part010SupportExplicit : Finset ℕ :=
  ([229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part010 : ℚ :=
  (71803528225 : ℚ) / 6757191808128

def SurrogateDiagonalTailChunk000Sub000Block004Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 229
    = surrogateDiagTailX0RatChunk000Sub000Block004Part010

theorem surrogateDiagonalTailChunk000Sub000Block004Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part010] using hcert

def TailChunk000Sub000Block004Part011SupportExplicit : Finset ℕ :=
  ([230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part011 : ℚ :=
  (27730929775 : ℚ) / 149953824768

def SurrogateDiagonalTailChunk000Sub000Block004Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 230
    = surrogateDiagTailX0RatChunk000Sub000Block004Part011

theorem surrogateDiagonalTailChunk000Sub000Block004Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part011] using hcert

def TailChunk000Sub000Block004Part012SupportExplicit : Finset ℕ :=
  ([231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part012 : ℚ :=
  (11188999 : ℚ) / 153630720

def SurrogateDiagonalTailChunk000Sub000Block004Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 231
    = surrogateDiagTailX0RatChunk000Sub000Block004Part012

theorem surrogateDiagonalTailChunk000Sub000Block004Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part012] using hcert

def TailChunk000Sub000Block004Part013SupportExplicit : Finset ℕ :=
  ([233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part013 : ℚ :=
  (74333856025 : ℚ) / 7244005951488

def SurrogateDiagonalTailChunk000Sub000Block004Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 233
    = surrogateDiagTailX0RatChunk000Sub000Block004Part013

theorem surrogateDiagonalTailChunk000Sub000Block004Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part013] using hcert

def TailChunk000Sub000Block004Part014SupportExplicit : Finset ℕ :=
  ([235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part014 : ℚ :=
  (18971095125 : ℚ) / 955381651456

def SurrogateDiagonalTailChunk000Sub000Block004Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 235
    = surrogateDiagTailX0RatChunk000Sub000Block004Part014

theorem surrogateDiagonalTailChunk000Sub000Block004Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part014] using hcert

def TailChunk000Sub000Block004Part015SupportExplicit : Finset ℕ :=
  ([237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part015 : ℚ :=
  (1617625 : ℚ) / 49353408

def SurrogateDiagonalTailChunk000Sub000Block004Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 237
    = surrogateDiagTailX0RatChunk000Sub000Block004Part015

theorem surrogateDiagonalTailChunk000Sub000Block004Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part015] using hcert

def TailChunk000Sub000Block004Part016SupportExplicit : Finset ℕ :=
  ([238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part016 : ℚ :=
  (3332687225 : ℚ) / 23597678592

def SurrogateDiagonalTailChunk000Sub000Block004Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 238
    = surrogateDiagTailX0RatChunk000Sub000Block004Part016

theorem surrogateDiagonalTailChunk000Sub000Block004Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part016] using hcert

def TailChunk000Sub000Block004Part017SupportExplicit : Finset ℕ :=
  ([239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part017 : ℚ :=
  (2092056625 : ℚ) / 235969444452

def SurrogateDiagonalTailChunk000Sub000Block004Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 239
    = surrogateDiagTailX0RatChunk000Sub000Block004Part017

theorem surrogateDiagonalTailChunk000Sub000Block004Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part017] using hcert

def TailChunk000Sub000Block004Part018SupportExplicit : Finset ℕ :=
  ([241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part018 : ℚ :=
  (33745061 : ℚ) / 3687137280

def SurrogateDiagonalTailChunk000Sub000Block004Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 241
    = surrogateDiagTailX0RatChunk000Sub000Block004Part018

theorem surrogateDiagonalTailChunk000Sub000Block004Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part018] using hcert

def TailChunk000Sub000Block004Part019SupportExplicit : Finset ℕ :=
  ([246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part019 : ℚ :=
  (496297559 : ℚ) / 2048409600

def SurrogateDiagonalTailChunk000Sub000Block004Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 246
    = surrogateDiagTailX0RatChunk000Sub000Block004Part019

theorem surrogateDiagonalTailChunk000Sub000Block004Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part019] using hcert

def TailChunk000Sub000Block004Part020SupportExplicit : Finset ℕ :=
  ([247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part020 : ℚ :=
  (8351546975 : ℚ) / 680380528896

def SurrogateDiagonalTailChunk000Sub000Block004Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 247
    = surrogateDiagTailX0RatChunk000Sub000Block004Part020

theorem surrogateDiagonalTailChunk000Sub000Block004Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part020] using hcert

def TailChunk000Sub000Block004Part021SupportExplicit : Finset ℕ :=
  ([249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part021 : ℚ :=
  (10209525 : ℚ) / 361697408

def SurrogateDiagonalTailChunk000Sub000Block004Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 249
    = surrogateDiagTailX0RatChunk000Sub000Block004Part021

theorem surrogateDiagonalTailChunk000Sub000Block004Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part021] using hcert

def TailChunk000Sub000Block004Part022SupportExplicit : Finset ℕ :=
  ([251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part022 : ℚ :=
  (2981774329 : ℚ) / 390703125000

def SurrogateDiagonalTailChunk000Sub000Block004Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 251
    = surrogateDiagTailX0RatChunk000Sub000Block004Part022

theorem surrogateDiagonalTailChunk000Sub000Block004Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part022] using hcert

def TailChunk000Sub000Block004Part023SupportExplicit : Finset ℕ :=
  ([253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part023 : ℚ :=
  (1389272993 : ℚ) / 117151425600

def SurrogateDiagonalTailChunk000Sub000Block004Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 253
    = surrogateDiagTailX0RatChunk000Sub000Block004Part023

theorem surrogateDiagonalTailChunk000Sub000Block004Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part023] using hcert

def TailChunk000Sub000Block004Part024SupportExplicit : Finset ℕ :=
  ([254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block004Part024 : ℚ :=
  (4335071975 : ℚ) / 70027162632

def SurrogateDiagonalTailChunk000Sub000Block004Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 254
    = surrogateDiagTailX0RatChunk000Sub000Block004Part024

theorem surrogateDiagonalTailChunk000Sub000Block004Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block004Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block004Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block004Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block004Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block004Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block004HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block004Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block004Part000
    + surrogateDiagTailX0RatChunk000Sub000Block004Part001
    + surrogateDiagTailX0RatChunk000Sub000Block004Part002
    + surrogateDiagTailX0RatChunk000Sub000Block004Part003
    + surrogateDiagTailX0RatChunk000Sub000Block004Part004
    + surrogateDiagTailX0RatChunk000Sub000Block004Part005
    + surrogateDiagTailX0RatChunk000Sub000Block004Part006
    + surrogateDiagTailX0RatChunk000Sub000Block004Part007
    + surrogateDiagTailX0RatChunk000Sub000Block004Part008
    + surrogateDiagTailX0RatChunk000Sub000Block004Part009

def surrogateDiagonalTailChunk000Sub000Block004MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block004Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block004Part010
    + surrogateDiagTailX0RatChunk000Sub000Block004Part011
    + surrogateDiagTailX0RatChunk000Sub000Block004Part012
    + surrogateDiagTailX0RatChunk000Sub000Block004Part013
    + surrogateDiagTailX0RatChunk000Sub000Block004Part014
    + surrogateDiagTailX0RatChunk000Sub000Block004Part015
    + surrogateDiagTailX0RatChunk000Sub000Block004Part016
    + surrogateDiagTailX0RatChunk000Sub000Block004Part017
    + surrogateDiagTailX0RatChunk000Sub000Block004Part018
    + surrogateDiagTailX0RatChunk000Sub000Block004Part019

def surrogateDiagonalTailChunk000Sub000Block004TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block004Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block004Part020
    + surrogateDiagTailX0RatChunk000Sub000Block004Part021
    + surrogateDiagTailX0RatChunk000Sub000Block004Part022
    + surrogateDiagTailX0RatChunk000Sub000Block004Part023
    + surrogateDiagTailX0RatChunk000Sub000Block004Part024

def surrogateDiagonalTailChunk000Sub000Block004Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block004HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block004MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block004TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block004 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block004Part000
    + surrogateDiagTailX0RatChunk000Sub000Block004Part001
    + surrogateDiagTailX0RatChunk000Sub000Block004Part002
    + surrogateDiagTailX0RatChunk000Sub000Block004Part003
    + surrogateDiagTailX0RatChunk000Sub000Block004Part004
    + surrogateDiagTailX0RatChunk000Sub000Block004Part005
    + surrogateDiagTailX0RatChunk000Sub000Block004Part006
    + surrogateDiagTailX0RatChunk000Sub000Block004Part007
    + surrogateDiagTailX0RatChunk000Sub000Block004Part008
    + surrogateDiagTailX0RatChunk000Sub000Block004Part009
    + surrogateDiagTailX0RatChunk000Sub000Block004Part010
    + surrogateDiagTailX0RatChunk000Sub000Block004Part011
    + surrogateDiagTailX0RatChunk000Sub000Block004Part012
    + surrogateDiagTailX0RatChunk000Sub000Block004Part013
    + surrogateDiagTailX0RatChunk000Sub000Block004Part014
    + surrogateDiagTailX0RatChunk000Sub000Block004Part015
    + surrogateDiagTailX0RatChunk000Sub000Block004Part016
    + surrogateDiagTailX0RatChunk000Sub000Block004Part017
    + surrogateDiagTailX0RatChunk000Sub000Block004Part018
    + surrogateDiagTailX0RatChunk000Sub000Block004Part019
    + surrogateDiagTailX0RatChunk000Sub000Block004Part020
    + surrogateDiagTailX0RatChunk000Sub000Block004Part021
    + surrogateDiagTailX0RatChunk000Sub000Block004Part022
    + surrogateDiagTailX0RatChunk000Sub000Block004Part023
    + surrogateDiagTailX0RatChunk000Sub000Block004Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block004_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block004Head + surrogateDiagTailX0RatChunk000Sub000Block004Mid + surrogateDiagTailX0RatChunk000Sub000Block004Tail =
      surrogateDiagTailX0RatChunk000Sub000Block004 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block004Head surrogateDiagTailX0RatChunk000Sub000Block004Mid surrogateDiagTailX0RatChunk000Sub000Block004Tail surrogateDiagTailX0RatChunk000Sub000Block004
  ring

def SurrogateDiagonalTailChunk000Sub000Block004HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block004HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block004Head

def SurrogateDiagonalTailChunk000Sub000Block004MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block004MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block004Mid

def SurrogateDiagonalTailChunk000Sub000Block004TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block004TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block004Tail

theorem surrogateDiagonalTailChunk000Sub000Block004_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block004HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block004MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block004TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block004Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block004 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block004HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block004MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block004TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block004Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block004_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
