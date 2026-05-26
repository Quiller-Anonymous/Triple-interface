import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [170,180). -/

/-- Block 170 covers tail-support indices [9250,9275) and q from 15265 to 15302. -/

def TailChunk000Sub001Block170Part000SupportExplicit : Finset ℕ :=
  ([15265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part000 : ℚ :=
  (1182911659 : ℚ) / 6073032193966080

def SurrogateDiagonalTailChunk000Sub001Block170Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15265
    = surrogateDiagTailX0RatChunk000Sub001Block170Part000

theorem surrogateDiagonalTailChunk000Sub001Block170Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part000] using hcert

def TailChunk000Sub001Block170Part001SupportExplicit : Finset ℕ :=
  ([15266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part001 : ℚ :=
  (139260957375 : ℚ) / 275047437893107712

def SurrogateDiagonalTailChunk000Sub001Block170Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15266
    = surrogateDiagTailX0RatChunk000Sub001Block170Part001

theorem surrogateDiagonalTailChunk000Sub001Block170Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part001] using hcert

def TailChunk000Sub001Block170Part002SupportExplicit : Finset ℕ :=
  ([15267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part002 : ℚ :=
  (23349193775 : ℚ) / 66687521183509248

def SurrogateDiagonalTailChunk000Sub001Block170Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15267
    = surrogateDiagTailX0RatChunk000Sub001Block170Part002

theorem surrogateDiagonalTailChunk000Sub001Block170Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part002] using hcert

def TailChunk000Sub001Block170Part003SupportExplicit : Finset ℕ :=
  ([15269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part003 : ℚ :=
  (3642849390625 : ℚ) / 33969994195690435872

def SurrogateDiagonalTailChunk000Sub001Block170Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15269
    = surrogateDiagTailX0RatChunk000Sub001Block170Part003

theorem surrogateDiagonalTailChunk000Sub001Block170Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part003] using hcert

def TailChunk000Sub001Block170Part004SupportExplicit : Finset ℕ :=
  ([15270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part004 : ℚ :=
  (759403311425 : ℚ) / 341044979208290304

def SurrogateDiagonalTailChunk000Sub001Block170Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15270
    = surrogateDiagTailX0RatChunk000Sub001Block170Part004

theorem surrogateDiagonalTailChunk000Sub001Block170Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part004] using hcert

def TailChunk000Sub001Block170Part005SupportExplicit : Finset ℕ :=
  ([15271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part005 : ℚ :=
  (5830086025 : ℚ) / 54380475214668882

def SurrogateDiagonalTailChunk000Sub001Block170Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15271
    = surrogateDiagTailX0RatChunk000Sub001Block170Part005

theorem surrogateDiagonalTailChunk000Sub001Block170Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part005] using hcert

def TailChunk000Sub001Block170Part006SupportExplicit : Finset ℕ :=
  ([15274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part006 : ℚ :=
  (6440691491 : ℚ) / 10165420269518400

def SurrogateDiagonalTailChunk000Sub001Block170Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15274
    = surrogateDiagTailX0RatChunk000Sub001Block170Part006

theorem surrogateDiagonalTailChunk000Sub001Block170Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part006] using hcert

def TailChunk000Sub001Block170Part007SupportExplicit : Finset ℕ :=
  ([15277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part007 : ℚ :=
  (3646667640625 : ℚ) / 34041247436449027872

def SurrogateDiagonalTailChunk000Sub001Block170Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15277
    = surrogateDiagTailX0RatChunk000Sub001Block170Part007

theorem surrogateDiagonalTailChunk000Sub001Block170Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part007] using hcert

def TailChunk000Sub001Block170Part008SupportExplicit : Finset ℕ :=
  ([15278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part008 : ℚ :=
  (911786265625 : ℚ) / 2127577964778064242

def SurrogateDiagonalTailChunk000Sub001Block170Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15278
    = surrogateDiagTailX0RatChunk000Sub001Block170Part008

theorem surrogateDiagonalTailChunk000Sub001Block170Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part008] using hcert

def TailChunk000Sub001Block170Part009SupportExplicit : Finset ℕ :=
  ([15279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part009 : ℚ :=
  (55957406233 : ℚ) / 182269811216908800

def SurrogateDiagonalTailChunk000Sub001Block170Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15279
    = surrogateDiagTailX0RatChunk000Sub001Block170Part009

theorem surrogateDiagonalTailChunk000Sub001Block170Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part009] using hcert

def TailChunk000Sub001Block170Part010SupportExplicit : Finset ℕ :=
  ([15281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part010 : ℚ :=
  (10244427067825 : ℚ) / 61596188269835747328

def SurrogateDiagonalTailChunk000Sub001Block170Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15281
    = surrogateDiagTailX0RatChunk000Sub001Block170Part010

theorem surrogateDiagonalTailChunk000Sub001Block170Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part010] using hcert

def TailChunk000Sub001Block170Part011SupportExplicit : Finset ℕ :=
  ([15283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part011 : ℚ :=
  (93841059881 : ℚ) / 652700462968995840

def SurrogateDiagonalTailChunk000Sub001Block170Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15283
    = surrogateDiagTailX0RatChunk000Sub001Block170Part011

theorem surrogateDiagonalTailChunk000Sub001Block170Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part011] using hcert

def TailChunk000Sub001Block170Part012SupportExplicit : Finset ℕ :=
  ([15285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part012 : ℚ :=
  (4601050039675 : ℚ) / 10999625998976974848

def SurrogateDiagonalTailChunk000Sub001Block170Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15285
    = surrogateDiagTailX0RatChunk000Sub001Block170Part012

theorem surrogateDiagonalTailChunk000Sub001Block170Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part012] using hcert

def TailChunk000Sub001Block170Part013SupportExplicit : Finset ℕ :=
  ([15286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part013 : ℚ :=
  (912741390625 : ℚ) / 2132038294411213362

def SurrogateDiagonalTailChunk000Sub001Block170Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15286
    = surrogateDiagTailX0RatChunk000Sub001Block170Part013

theorem surrogateDiagonalTailChunk000Sub001Block170Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part013] using hcert

def TailChunk000Sub001Block170Part014SupportExplicit : Finset ℕ :=
  ([15287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part014 : ℚ :=
  (3651443265625 : ℚ) / 34130471548079753202

def SurrogateDiagonalTailChunk000Sub001Block170Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15287
    = surrogateDiagTailX0RatChunk000Sub001Block170Part014

theorem surrogateDiagonalTailChunk000Sub001Block170Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part014] using hcert

def TailChunk000Sub001Block170Part015SupportExplicit : Finset ℕ :=
  ([15289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part015 : ℚ :=
  (3652398765625 : ℚ) / 34148337396835963392

def SurrogateDiagonalTailChunk000Sub001Block170Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15289
    = surrogateDiagTailX0RatChunk000Sub001Block170Part015

theorem surrogateDiagonalTailChunk000Sub001Block170Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part015] using hcert

def TailChunk000Sub001Block170Part016SupportExplicit : Finset ℕ :=
  ([15290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part016 : ℚ :=
  (5114611069 : ℚ) / 5159060917862400

def SurrogateDiagonalTailChunk000Sub001Block170Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15290
    = surrogateDiagTailX0RatChunk000Sub001Block170Part016

theorem surrogateDiagonalTailChunk000Sub001Block170Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part016] using hcert

def TailChunk000Sub001Block170Part017SupportExplicit : Finset ℕ :=
  ([15293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part017 : ℚ :=
  (186080265371 : ℚ) / 1634471379822182400

def SurrogateDiagonalTailChunk000Sub001Block170Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15293
    = surrogateDiagTailX0RatChunk000Sub001Block170Part017

theorem surrogateDiagonalTailChunk000Sub001Block170Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part017] using hcert

def TailChunk000Sub001Block170Part018SupportExplicit : Finset ℕ :=
  ([15294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part018 : ℚ :=
  (1014897244475 : ℚ) / 843168824613233664

def SurrogateDiagonalTailChunk000Sub001Block170Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15294
    = surrogateDiagTailX0RatChunk000Sub001Block170Part018

theorem surrogateDiagonalTailChunk000Sub001Block170Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part018] using hcert

def TailChunk000Sub001Block170Part019SupportExplicit : Finset ℕ :=
  ([15295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part019 : ℚ :=
  (2214034943225 : ℚ) / 6800350770221285376

def SurrogateDiagonalTailChunk000Sub001Block170Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15295
    = surrogateDiagTailX0RatChunk000Sub001Block170Part019

theorem surrogateDiagonalTailChunk000Sub001Block170Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part019] using hcert

def TailChunk000Sub001Block170Part020SupportExplicit : Finset ℕ :=
  ([15297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part020 : ℚ :=
  (6498025490125 : ℚ) / 27023784319201254528

def SurrogateDiagonalTailChunk000Sub001Block170Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15297
    = surrogateDiagTailX0RatChunk000Sub001Block170Part020

theorem surrogateDiagonalTailChunk000Sub001Block170Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part020] using hcert

def TailChunk000Sub001Block170Part021SupportExplicit : Finset ℕ :=
  ([15298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part021 : ℚ :=
  (914175015625 : ℚ) / 2138741933819953152

def SurrogateDiagonalTailChunk000Sub001Block170Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15298
    = surrogateDiagTailX0RatChunk000Sub001Block170Part021

theorem surrogateDiagonalTailChunk000Sub001Block170Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part021] using hcert

def TailChunk000Sub001Block170Part022SupportExplicit : Finset ℕ :=
  ([15299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part022 : ℚ :=
  (3657178140625 : ℚ) / 34237771873681718802

def SurrogateDiagonalTailChunk000Sub001Block170Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15299
    = surrogateDiagTailX0RatChunk000Sub001Block170Part022

theorem surrogateDiagonalTailChunk000Sub001Block170Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part022] using hcert

def TailChunk000Sub001Block170Part023SupportExplicit : Finset ℕ :=
  ([15301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part023 : ℚ :=
  (107618079007 : ℚ) / 654598949675212800

def SurrogateDiagonalTailChunk000Sub001Block170Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15301
    = surrogateDiagTailX0RatChunk000Sub001Block170Part023

theorem surrogateDiagonalTailChunk000Sub001Block170Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part023] using hcert

def TailChunk000Sub001Block170Part024SupportExplicit : Finset ℕ :=
  ([15302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block170Part024 : ℚ :=
  (2983568647375 : ℚ) / 4608105504612599808

def SurrogateDiagonalTailChunk000Sub001Block170Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15302
    = surrogateDiagTailX0RatChunk000Sub001Block170Part024

theorem surrogateDiagonalTailChunk000Sub001Block170Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block170Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block170Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block170Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block170Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block170Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block170Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block170HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block170Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block170Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block170Part000
    + surrogateDiagTailX0RatChunk000Sub001Block170Part001
    + surrogateDiagTailX0RatChunk000Sub001Block170Part002
    + surrogateDiagTailX0RatChunk000Sub001Block170Part003
    + surrogateDiagTailX0RatChunk000Sub001Block170Part004
    + surrogateDiagTailX0RatChunk000Sub001Block170Part005
    + surrogateDiagTailX0RatChunk000Sub001Block170Part006
    + surrogateDiagTailX0RatChunk000Sub001Block170Part007
    + surrogateDiagTailX0RatChunk000Sub001Block170Part008
    + surrogateDiagTailX0RatChunk000Sub001Block170Part009

def surrogateDiagonalTailChunk000Sub001Block170MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block170Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block170Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block170Part010
    + surrogateDiagTailX0RatChunk000Sub001Block170Part011
    + surrogateDiagTailX0RatChunk000Sub001Block170Part012
    + surrogateDiagTailX0RatChunk000Sub001Block170Part013
    + surrogateDiagTailX0RatChunk000Sub001Block170Part014
    + surrogateDiagTailX0RatChunk000Sub001Block170Part015
    + surrogateDiagTailX0RatChunk000Sub001Block170Part016
    + surrogateDiagTailX0RatChunk000Sub001Block170Part017
    + surrogateDiagTailX0RatChunk000Sub001Block170Part018
    + surrogateDiagTailX0RatChunk000Sub001Block170Part019

def surrogateDiagonalTailChunk000Sub001Block170TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block170Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block170Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block170Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block170Part020
    + surrogateDiagTailX0RatChunk000Sub001Block170Part021
    + surrogateDiagTailX0RatChunk000Sub001Block170Part022
    + surrogateDiagTailX0RatChunk000Sub001Block170Part023
    + surrogateDiagTailX0RatChunk000Sub001Block170Part024

def surrogateDiagonalTailChunk000Sub001Block170Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block170HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block170MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block170TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block170 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block170Part000
    + surrogateDiagTailX0RatChunk000Sub001Block170Part001
    + surrogateDiagTailX0RatChunk000Sub001Block170Part002
    + surrogateDiagTailX0RatChunk000Sub001Block170Part003
    + surrogateDiagTailX0RatChunk000Sub001Block170Part004
    + surrogateDiagTailX0RatChunk000Sub001Block170Part005
    + surrogateDiagTailX0RatChunk000Sub001Block170Part006
    + surrogateDiagTailX0RatChunk000Sub001Block170Part007
    + surrogateDiagTailX0RatChunk000Sub001Block170Part008
    + surrogateDiagTailX0RatChunk000Sub001Block170Part009
    + surrogateDiagTailX0RatChunk000Sub001Block170Part010
    + surrogateDiagTailX0RatChunk000Sub001Block170Part011
    + surrogateDiagTailX0RatChunk000Sub001Block170Part012
    + surrogateDiagTailX0RatChunk000Sub001Block170Part013
    + surrogateDiagTailX0RatChunk000Sub001Block170Part014
    + surrogateDiagTailX0RatChunk000Sub001Block170Part015
    + surrogateDiagTailX0RatChunk000Sub001Block170Part016
    + surrogateDiagTailX0RatChunk000Sub001Block170Part017
    + surrogateDiagTailX0RatChunk000Sub001Block170Part018
    + surrogateDiagTailX0RatChunk000Sub001Block170Part019
    + surrogateDiagTailX0RatChunk000Sub001Block170Part020
    + surrogateDiagTailX0RatChunk000Sub001Block170Part021
    + surrogateDiagTailX0RatChunk000Sub001Block170Part022
    + surrogateDiagTailX0RatChunk000Sub001Block170Part023
    + surrogateDiagTailX0RatChunk000Sub001Block170Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block170_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block170Head + surrogateDiagTailX0RatChunk000Sub001Block170Mid + surrogateDiagTailX0RatChunk000Sub001Block170Tail =
      surrogateDiagTailX0RatChunk000Sub001Block170 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block170Head surrogateDiagTailX0RatChunk000Sub001Block170Mid surrogateDiagTailX0RatChunk000Sub001Block170Tail surrogateDiagTailX0RatChunk000Sub001Block170
  ring

def SurrogateDiagonalTailChunk000Sub001Block170HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block170HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block170Head

def SurrogateDiagonalTailChunk000Sub001Block170MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block170MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block170Mid

def SurrogateDiagonalTailChunk000Sub001Block170TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block170TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block170Tail

theorem surrogateDiagonalTailChunk000Sub001Block170_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block170HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block170MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block170TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block170Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block170 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block170HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block170MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block170TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block170Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block170_eq_head_add_mid_add_tail

/-- Block 171 covers tail-support indices [9275,9300) and q from 15303 to 15346. -/

def TailChunk000Sub001Block171Part000SupportExplicit : Finset ℕ :=
  ([15303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part000 : ℚ :=
  (260124979597 : ℚ) / 1082648646432000000

def SurrogateDiagonalTailChunk000Sub001Block171Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15303
    = surrogateDiagTailX0RatChunk000Sub001Block171Part000

theorem surrogateDiagonalTailChunk000Sub001Block171Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part000] using hcert

def TailChunk000Sub001Block171Part001SupportExplicit : Finset ℕ :=
  ([15305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part001 : ℚ :=
  (4691806439 : ℚ) / 448996046648279040

def SurrogateDiagonalTailChunk000Sub001Block171Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15305
    = surrogateDiagTailX0RatChunk000Sub001Block171Part001

theorem surrogateDiagonalTailChunk000Sub001Block171Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part001] using hcert

def TailChunk000Sub001Block171Part002SupportExplicit : Finset ℕ :=
  ([15306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part002 : ℚ :=
  (325625099 : ℚ) / 1353310808040000

def SurrogateDiagonalTailChunk000Sub001Block171Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15306
    = surrogateDiagTailX0RatChunk000Sub001Block171Part002

theorem surrogateDiagonalTailChunk000Sub001Block171Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part002] using hcert

def TailChunk000Sub001Block171Part003SupportExplicit : Finset ℕ :=
  ([15307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block171Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15307
    = surrogateDiagTailX0RatChunk000Sub001Block171Part003

theorem surrogateDiagonalTailChunk000Sub001Block171Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part003] using hcert

def TailChunk000Sub001Block171Part004SupportExplicit : Finset ℕ :=
  ([15310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part004 : ℚ :=
  (4399934413 : ℚ) / 35077816144396800

def SurrogateDiagonalTailChunk000Sub001Block171Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15310
    = surrogateDiagTailX0RatChunk000Sub001Block171Part004

theorem surrogateDiagonalTailChunk000Sub001Block171Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part004] using hcert

def TailChunk000Sub001Block171Part005SupportExplicit : Finset ℕ :=
  ([15311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part005 : ℚ :=
  (24722449 : ℚ) / 33756750000000000

def SurrogateDiagonalTailChunk000Sub001Block171Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15311
    = surrogateDiagTailX0RatChunk000Sub001Block171Part005

theorem surrogateDiagonalTailChunk000Sub001Block171Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part005] using hcert

def TailChunk000Sub001Block171Part006SupportExplicit : Finset ℕ :=
  ([15313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block171Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15313
    = surrogateDiagTailX0RatChunk000Sub001Block171Part006

theorem surrogateDiagonalTailChunk000Sub001Block171Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part006] using hcert

def TailChunk000Sub001Block171Part007SupportExplicit : Finset ℕ :=
  ([15314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part007 : ℚ :=
  (13733085007 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub001Block171Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15314
    = surrogateDiagTailX0RatChunk000Sub001Block171Part007

theorem surrogateDiagonalTailChunk000Sub001Block171Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part007] using hcert

def TailChunk000Sub001Block171Part008SupportExplicit : Finset ℕ :=
  ([15315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part008 : ℚ :=
  (11986054337 : ℚ) / 88690577115709440

def SurrogateDiagonalTailChunk000Sub001Block171Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15315
    = surrogateDiagTailX0RatChunk000Sub001Block171Part008

theorem surrogateDiagonalTailChunk000Sub001Block171Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part008] using hcert

def TailChunk000Sub001Block171Part009SupportExplicit : Finset ℕ :=
  ([15319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block171Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15319
    = surrogateDiagTailX0RatChunk000Sub001Block171Part009

theorem surrogateDiagonalTailChunk000Sub001Block171Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part009] using hcert

def TailChunk000Sub001Block171Part010SupportExplicit : Finset ℕ :=
  ([15321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part010 : ℚ :=
  (815038654925 : ℚ) / 13596905768740190784

def SurrogateDiagonalTailChunk000Sub001Block171Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15321
    = surrogateDiagTailX0RatChunk000Sub001Block171Part010

theorem surrogateDiagonalTailChunk000Sub001Block171Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part010] using hcert

def TailChunk000Sub001Block171Part011SupportExplicit : Finset ℕ :=
  ([15322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part011 : ℚ :=
  (1351385825 : ℚ) / 160648622651350296

def SurrogateDiagonalTailChunk000Sub001Block171Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15322
    = surrogateDiagTailX0RatChunk000Sub001Block171Part011

theorem surrogateDiagonalTailChunk000Sub001Block171Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part011] using hcert

def TailChunk000Sub001Block171Part012SupportExplicit : Finset ℕ :=
  ([15323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part012 : ℚ :=
  (36322250233 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk000Sub001Block171Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15323
    = surrogateDiagTailX0RatChunk000Sub001Block171Part012

theorem surrogateDiagonalTailChunk000Sub001Block171Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part012] using hcert

def TailChunk000Sub001Block171Part013SupportExplicit : Finset ℕ :=
  ([15326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part013 : ℚ :=
  (53908962625 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk000Sub001Block171Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15326
    = surrogateDiagTailX0RatChunk000Sub001Block171Part013

theorem surrogateDiagonalTailChunk000Sub001Block171Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part013] using hcert

def TailChunk000Sub001Block171Part014SupportExplicit : Finset ℕ :=
  ([15329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block171Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15329
    = surrogateDiagTailX0RatChunk000Sub001Block171Part014

theorem surrogateDiagonalTailChunk000Sub001Block171Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part014] using hcert

def TailChunk000Sub001Block171Part015SupportExplicit : Finset ℕ :=
  ([15330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part015 : ℚ :=
  (377366560025 : ℚ) / 178357673366913024

def SurrogateDiagonalTailChunk000Sub001Block171Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15330
    = surrogateDiagTailX0RatChunk000Sub001Block171Part015

theorem surrogateDiagonalTailChunk000Sub001Block171Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part015] using hcert

def TailChunk000Sub001Block171Part016SupportExplicit : Finset ℕ :=
  ([15331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block171Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15331
    = surrogateDiagTailX0RatChunk000Sub001Block171Part016

theorem surrogateDiagonalTailChunk000Sub001Block171Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part016] using hcert

def TailChunk000Sub001Block171Part017SupportExplicit : Finset ℕ :=
  ([15333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part017 : ℚ :=
  (1627311527275 : ℚ) / 21665865266294980608

def SurrogateDiagonalTailChunk000Sub001Block171Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15333
    = surrogateDiagTailX0RatChunk000Sub001Block171Part017

theorem surrogateDiagonalTailChunk000Sub001Block171Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part017] using hcert

def TailChunk000Sub001Block171Part018SupportExplicit : Finset ℕ :=
  ([15334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part018 : ℚ :=
  (2796790901 : ℚ) / 33561142886400000

def SurrogateDiagonalTailChunk000Sub001Block171Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15334
    = surrogateDiagTailX0RatChunk000Sub001Block171Part018

theorem surrogateDiagonalTailChunk000Sub001Block171Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part018] using hcert

def TailChunk000Sub001Block171Part019SupportExplicit : Finset ℕ :=
  ([15335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part019 : ℚ :=
  (588773054125 : ℚ) / 56565994409805662208

def SurrogateDiagonalTailChunk000Sub001Block171Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15335
    = surrogateDiagTailX0RatChunk000Sub001Block171Part019

theorem surrogateDiagonalTailChunk000Sub001Block171Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part019] using hcert

def TailChunk000Sub001Block171Part020SupportExplicit : Finset ℕ :=
  ([15338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block171Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15338
    = surrogateDiagTailX0RatChunk000Sub001Block171Part020

theorem surrogateDiagonalTailChunk000Sub001Block171Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part020] using hcert

def TailChunk000Sub001Block171Part021SupportExplicit : Finset ℕ :=
  ([15339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part021 : ℚ :=
  (408477264925 : ℚ) / 6830464378831183872

def SurrogateDiagonalTailChunk000Sub001Block171Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15339
    = surrogateDiagTailX0RatChunk000Sub001Block171Part021

theorem surrogateDiagonalTailChunk000Sub001Block171Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part021] using hcert

def TailChunk000Sub001Block171Part022SupportExplicit : Finset ℕ :=
  ([15342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part022 : ℚ :=
  (408551770475 : ℚ) / 853808047353897984

def SurrogateDiagonalTailChunk000Sub001Block171Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15342
    = surrogateDiagTailX0RatChunk000Sub001Block171Part022

theorem surrogateDiagonalTailChunk000Sub001Block171Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part022] using hcert

def TailChunk000Sub001Block171Part023SupportExplicit : Finset ℕ :=
  ([15343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part023 : ℚ :=
  (604614425 : ℚ) / 843525859609154304

def SurrogateDiagonalTailChunk000Sub001Block171Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15343
    = surrogateDiagTailX0RatChunk000Sub001Block171Part023

theorem surrogateDiagonalTailChunk000Sub001Block171Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part023] using hcert

def TailChunk000Sub001Block171Part024SupportExplicit : Finset ℕ :=
  ([15346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block171Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block171Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15346
    = surrogateDiagTailX0RatChunk000Sub001Block171Part024

theorem surrogateDiagonalTailChunk000Sub001Block171Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block171Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block171Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block171Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block171Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block171Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block171Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block171HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block171Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block171Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block171Part000
    + surrogateDiagTailX0RatChunk000Sub001Block171Part001
    + surrogateDiagTailX0RatChunk000Sub001Block171Part002
    + surrogateDiagTailX0RatChunk000Sub001Block171Part003
    + surrogateDiagTailX0RatChunk000Sub001Block171Part004
    + surrogateDiagTailX0RatChunk000Sub001Block171Part005
    + surrogateDiagTailX0RatChunk000Sub001Block171Part006
    + surrogateDiagTailX0RatChunk000Sub001Block171Part007
    + surrogateDiagTailX0RatChunk000Sub001Block171Part008
    + surrogateDiagTailX0RatChunk000Sub001Block171Part009

def surrogateDiagonalTailChunk000Sub001Block171MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block171Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block171Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block171Part010
    + surrogateDiagTailX0RatChunk000Sub001Block171Part011
    + surrogateDiagTailX0RatChunk000Sub001Block171Part012
    + surrogateDiagTailX0RatChunk000Sub001Block171Part013
    + surrogateDiagTailX0RatChunk000Sub001Block171Part014
    + surrogateDiagTailX0RatChunk000Sub001Block171Part015
    + surrogateDiagTailX0RatChunk000Sub001Block171Part016
    + surrogateDiagTailX0RatChunk000Sub001Block171Part017
    + surrogateDiagTailX0RatChunk000Sub001Block171Part018
    + surrogateDiagTailX0RatChunk000Sub001Block171Part019

def surrogateDiagonalTailChunk000Sub001Block171TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block171Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block171Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block171Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block171Part020
    + surrogateDiagTailX0RatChunk000Sub001Block171Part021
    + surrogateDiagTailX0RatChunk000Sub001Block171Part022
    + surrogateDiagTailX0RatChunk000Sub001Block171Part023
    + surrogateDiagTailX0RatChunk000Sub001Block171Part024

def surrogateDiagonalTailChunk000Sub001Block171Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block171HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block171MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block171TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block171 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block171Part000
    + surrogateDiagTailX0RatChunk000Sub001Block171Part001
    + surrogateDiagTailX0RatChunk000Sub001Block171Part002
    + surrogateDiagTailX0RatChunk000Sub001Block171Part003
    + surrogateDiagTailX0RatChunk000Sub001Block171Part004
    + surrogateDiagTailX0RatChunk000Sub001Block171Part005
    + surrogateDiagTailX0RatChunk000Sub001Block171Part006
    + surrogateDiagTailX0RatChunk000Sub001Block171Part007
    + surrogateDiagTailX0RatChunk000Sub001Block171Part008
    + surrogateDiagTailX0RatChunk000Sub001Block171Part009
    + surrogateDiagTailX0RatChunk000Sub001Block171Part010
    + surrogateDiagTailX0RatChunk000Sub001Block171Part011
    + surrogateDiagTailX0RatChunk000Sub001Block171Part012
    + surrogateDiagTailX0RatChunk000Sub001Block171Part013
    + surrogateDiagTailX0RatChunk000Sub001Block171Part014
    + surrogateDiagTailX0RatChunk000Sub001Block171Part015
    + surrogateDiagTailX0RatChunk000Sub001Block171Part016
    + surrogateDiagTailX0RatChunk000Sub001Block171Part017
    + surrogateDiagTailX0RatChunk000Sub001Block171Part018
    + surrogateDiagTailX0RatChunk000Sub001Block171Part019
    + surrogateDiagTailX0RatChunk000Sub001Block171Part020
    + surrogateDiagTailX0RatChunk000Sub001Block171Part021
    + surrogateDiagTailX0RatChunk000Sub001Block171Part022
    + surrogateDiagTailX0RatChunk000Sub001Block171Part023
    + surrogateDiagTailX0RatChunk000Sub001Block171Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block171_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block171Head + surrogateDiagTailX0RatChunk000Sub001Block171Mid + surrogateDiagTailX0RatChunk000Sub001Block171Tail =
      surrogateDiagTailX0RatChunk000Sub001Block171 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block171Head surrogateDiagTailX0RatChunk000Sub001Block171Mid surrogateDiagTailX0RatChunk000Sub001Block171Tail surrogateDiagTailX0RatChunk000Sub001Block171
  ring

def SurrogateDiagonalTailChunk000Sub001Block171HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block171HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block171Head

def SurrogateDiagonalTailChunk000Sub001Block171MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block171MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block171Mid

def SurrogateDiagonalTailChunk000Sub001Block171TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block171TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block171Tail

theorem surrogateDiagonalTailChunk000Sub001Block171_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block171HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block171MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block171TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block171Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block171 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block171HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block171MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block171TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block171Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block171_eq_head_add_mid_add_tail

/-- Block 172 covers tail-support indices [9300,9325) and q from 15347 to 15391. -/

def TailChunk000Sub001Block172Part000SupportExplicit : Finset ℕ :=
  ([15347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part000 : ℚ :=
  (77767424575 : ℚ) / 129859703670121187328

def SurrogateDiagonalTailChunk000Sub001Block172Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15347
    = surrogateDiagTailX0RatChunk000Sub001Block172Part000

theorem surrogateDiagonalTailChunk000Sub001Block172Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part000] using hcert

def TailChunk000Sub001Block172Part001SupportExplicit : Finset ℕ :=
  ([15349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15349
    = surrogateDiagTailX0RatChunk000Sub001Block172Part001

theorem surrogateDiagonalTailChunk000Sub001Block172Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part001] using hcert

def TailChunk000Sub001Block172Part002SupportExplicit : Finset ℕ :=
  ([15351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part002 : ℚ :=
  (824778601175 : ℚ) / 5286873750048866304

def SurrogateDiagonalTailChunk000Sub001Block172Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15351
    = surrogateDiagTailX0RatChunk000Sub001Block172Part002

theorem surrogateDiagonalTailChunk000Sub001Block172Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part002] using hcert

def TailChunk000Sub001Block172Part003SupportExplicit : Finset ℕ :=
  ([15353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part003 : ℚ :=
  (2344294639 : ℚ) / 670175602174771200

def SurrogateDiagonalTailChunk000Sub001Block172Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15353
    = surrogateDiagTailX0RatChunk000Sub001Block172Part003

theorem surrogateDiagonalTailChunk000Sub001Block172Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part003] using hcert

def TailChunk000Sub001Block172Part004SupportExplicit : Finset ℕ :=
  ([15355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part004 : ℚ :=
  (45698657575 : ℚ) / 1800397796106829824

def SurrogateDiagonalTailChunk000Sub001Block172Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15355
    = surrogateDiagTailX0RatChunk000Sub001Block172Part004

theorem surrogateDiagonalTailChunk000Sub001Block172Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part004] using hcert

def TailChunk000Sub001Block172Part005SupportExplicit : Finset ℕ :=
  ([15357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part005 : ℚ :=
  (818872654775 : ℚ) / 13725177576973591104

def SurrogateDiagonalTailChunk000Sub001Block172Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15357
    = surrogateDiagTailX0RatChunk000Sub001Block172Part005

theorem surrogateDiagonalTailChunk000Sub001Block172Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part005] using hcert

def TailChunk000Sub001Block172Part006SupportExplicit : Finset ℕ :=
  ([15358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part006 : ℚ :=
  (376953921775 : ℚ) / 4675995418926809088

def SurrogateDiagonalTailChunk000Sub001Block172Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15358
    = surrogateDiagTailX0RatChunk000Sub001Block172Part006

theorem surrogateDiagonalTailChunk000Sub001Block172Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part006] using hcert

def TailChunk000Sub001Block172Part007SupportExplicit : Finset ℕ :=
  ([15359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15359
    = surrogateDiagTailX0RatChunk000Sub001Block172Part007

theorem surrogateDiagonalTailChunk000Sub001Block172Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part007] using hcert

def TailChunk000Sub001Block172Part008SupportExplicit : Finset ℕ :=
  ([15361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15361
    = surrogateDiagTailX0RatChunk000Sub001Block172Part008

theorem surrogateDiagonalTailChunk000Sub001Block172Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part008] using hcert

def TailChunk000Sub001Block172Part009SupportExplicit : Finset ℕ :=
  ([15362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15362
    = surrogateDiagTailX0RatChunk000Sub001Block172Part009

theorem surrogateDiagonalTailChunk000Sub001Block172Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part009] using hcert

def TailChunk000Sub001Block172Part010SupportExplicit : Finset ℕ :=
  ([15365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part010 : ℚ :=
  (1529868162325 : ℚ) / 30532914933406138368

def SurrogateDiagonalTailChunk000Sub001Block172Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15365
    = surrogateDiagTailX0RatChunk000Sub001Block172Part010

theorem surrogateDiagonalTailChunk000Sub001Block172Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part010] using hcert

def TailChunk000Sub001Block172Part011SupportExplicit : Finset ℕ :=
  ([15366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part011 : ℚ :=
  (811672890625 : ℚ) / 1224323290303561728

def SurrogateDiagonalTailChunk000Sub001Block172Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15366
    = surrogateDiagTailX0RatChunk000Sub001Block172Part011

theorem surrogateDiagonalTailChunk000Sub001Block172Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part011] using hcert

def TailChunk000Sub001Block172Part012SupportExplicit : Finset ℕ :=
  ([15369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part012 : ℚ :=
  (818285867225 : ℚ) / 12185495525554274304

def SurrogateDiagonalTailChunk000Sub001Block172Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15369
    = surrogateDiagTailX0RatChunk000Sub001Block172Part012

theorem surrogateDiagonalTailChunk000Sub001Block172Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part012] using hcert

def TailChunk000Sub001Block172Part013SupportExplicit : Finset ℕ :=
  ([15370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part013 : ℚ :=
  (247748638175 : ℚ) / 1438408790343942144

def SurrogateDiagonalTailChunk000Sub001Block172Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15370
    = surrogateDiagTailX0RatChunk000Sub001Block172Part013

theorem surrogateDiagonalTailChunk000Sub001Block172Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part013] using hcert

def TailChunk000Sub001Block172Part014SupportExplicit : Finset ℕ :=
  ([15371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part014 : ℚ :=
  (125100778925 : ℚ) / 55941270652452225024

def SurrogateDiagonalTailChunk000Sub001Block172Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15371
    = surrogateDiagTailX0RatChunk000Sub001Block172Part014

theorem surrogateDiagonalTailChunk000Sub001Block172Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part014] using hcert

def TailChunk000Sub001Block172Part015SupportExplicit : Finset ℕ :=
  ([15373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15373
    = surrogateDiagTailX0RatChunk000Sub001Block172Part015

theorem surrogateDiagonalTailChunk000Sub001Block172Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part015] using hcert

def TailChunk000Sub001Block172Part016SupportExplicit : Finset ℕ :=
  ([15374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15374
    = surrogateDiagTailX0RatChunk000Sub001Block172Part016

theorem surrogateDiagonalTailChunk000Sub001Block172Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part016] using hcert

def TailChunk000Sub001Block172Part017SupportExplicit : Finset ℕ :=
  ([15377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15377
    = surrogateDiagTailX0RatChunk000Sub001Block172Part017

theorem surrogateDiagonalTailChunk000Sub001Block172Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part017] using hcert

def TailChunk000Sub001Block172Part018SupportExplicit : Finset ℕ :=
  ([15378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part018 : ℚ :=
  (32673346159 : ℚ) / 46361638089523200

def SurrogateDiagonalTailChunk000Sub001Block172Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15378
    = surrogateDiagTailX0RatChunk000Sub001Block172Part018

theorem surrogateDiagonalTailChunk000Sub001Block172Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part018] using hcert

def TailChunk000Sub001Block172Part019SupportExplicit : Finset ℕ :=
  ([15382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15382
    = surrogateDiagTailX0RatChunk000Sub001Block172Part019

theorem surrogateDiagonalTailChunk000Sub001Block172Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part019] using hcert

def TailChunk000Sub001Block172Part020SupportExplicit : Finset ℕ :=
  ([15383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15383
    = surrogateDiagTailX0RatChunk000Sub001Block172Part020

theorem surrogateDiagonalTailChunk000Sub001Block172Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part020] using hcert

def TailChunk000Sub001Block172Part021SupportExplicit : Finset ℕ :=
  ([15385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part021 : ℚ :=
  (12914275549 : ℚ) / 440389316955340800

def SurrogateDiagonalTailChunk000Sub001Block172Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15385
    = surrogateDiagTailX0RatChunk000Sub001Block172Part021

theorem surrogateDiagonalTailChunk000Sub001Block172Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part021] using hcert

def TailChunk000Sub001Block172Part022SupportExplicit : Finset ℕ :=
  ([15387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part022 : ℚ :=
  (1633903666375 : ℚ) / 22764046424662591488

def SurrogateDiagonalTailChunk000Sub001Block172Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15387
    = surrogateDiagTailX0RatChunk000Sub001Block172Part022

theorem surrogateDiagonalTailChunk000Sub001Block172Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part022] using hcert

def TailChunk000Sub001Block172Part023SupportExplicit : Finset ℕ :=
  ([15389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part023 : ℚ :=
  (14777269927 : ℚ) / 3820458934215043200

def SurrogateDiagonalTailChunk000Sub001Block172Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15389
    = surrogateDiagTailX0RatChunk000Sub001Block172Part023

theorem surrogateDiagonalTailChunk000Sub001Block172Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part023] using hcert

def TailChunk000Sub001Block172Part024SupportExplicit : Finset ℕ :=
  ([15391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block172Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block172Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15391
    = surrogateDiagTailX0RatChunk000Sub001Block172Part024

theorem surrogateDiagonalTailChunk000Sub001Block172Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block172Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block172Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block172Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block172Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block172Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block172Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block172HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block172Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block172Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block172Part000
    + surrogateDiagTailX0RatChunk000Sub001Block172Part001
    + surrogateDiagTailX0RatChunk000Sub001Block172Part002
    + surrogateDiagTailX0RatChunk000Sub001Block172Part003
    + surrogateDiagTailX0RatChunk000Sub001Block172Part004
    + surrogateDiagTailX0RatChunk000Sub001Block172Part005
    + surrogateDiagTailX0RatChunk000Sub001Block172Part006
    + surrogateDiagTailX0RatChunk000Sub001Block172Part007
    + surrogateDiagTailX0RatChunk000Sub001Block172Part008
    + surrogateDiagTailX0RatChunk000Sub001Block172Part009

def surrogateDiagonalTailChunk000Sub001Block172MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block172Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block172Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block172Part010
    + surrogateDiagTailX0RatChunk000Sub001Block172Part011
    + surrogateDiagTailX0RatChunk000Sub001Block172Part012
    + surrogateDiagTailX0RatChunk000Sub001Block172Part013
    + surrogateDiagTailX0RatChunk000Sub001Block172Part014
    + surrogateDiagTailX0RatChunk000Sub001Block172Part015
    + surrogateDiagTailX0RatChunk000Sub001Block172Part016
    + surrogateDiagTailX0RatChunk000Sub001Block172Part017
    + surrogateDiagTailX0RatChunk000Sub001Block172Part018
    + surrogateDiagTailX0RatChunk000Sub001Block172Part019

def surrogateDiagonalTailChunk000Sub001Block172TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block172Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block172Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block172Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block172Part020
    + surrogateDiagTailX0RatChunk000Sub001Block172Part021
    + surrogateDiagTailX0RatChunk000Sub001Block172Part022
    + surrogateDiagTailX0RatChunk000Sub001Block172Part023
    + surrogateDiagTailX0RatChunk000Sub001Block172Part024

def surrogateDiagonalTailChunk000Sub001Block172Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block172HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block172MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block172TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block172 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block172Part000
    + surrogateDiagTailX0RatChunk000Sub001Block172Part001
    + surrogateDiagTailX0RatChunk000Sub001Block172Part002
    + surrogateDiagTailX0RatChunk000Sub001Block172Part003
    + surrogateDiagTailX0RatChunk000Sub001Block172Part004
    + surrogateDiagTailX0RatChunk000Sub001Block172Part005
    + surrogateDiagTailX0RatChunk000Sub001Block172Part006
    + surrogateDiagTailX0RatChunk000Sub001Block172Part007
    + surrogateDiagTailX0RatChunk000Sub001Block172Part008
    + surrogateDiagTailX0RatChunk000Sub001Block172Part009
    + surrogateDiagTailX0RatChunk000Sub001Block172Part010
    + surrogateDiagTailX0RatChunk000Sub001Block172Part011
    + surrogateDiagTailX0RatChunk000Sub001Block172Part012
    + surrogateDiagTailX0RatChunk000Sub001Block172Part013
    + surrogateDiagTailX0RatChunk000Sub001Block172Part014
    + surrogateDiagTailX0RatChunk000Sub001Block172Part015
    + surrogateDiagTailX0RatChunk000Sub001Block172Part016
    + surrogateDiagTailX0RatChunk000Sub001Block172Part017
    + surrogateDiagTailX0RatChunk000Sub001Block172Part018
    + surrogateDiagTailX0RatChunk000Sub001Block172Part019
    + surrogateDiagTailX0RatChunk000Sub001Block172Part020
    + surrogateDiagTailX0RatChunk000Sub001Block172Part021
    + surrogateDiagTailX0RatChunk000Sub001Block172Part022
    + surrogateDiagTailX0RatChunk000Sub001Block172Part023
    + surrogateDiagTailX0RatChunk000Sub001Block172Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block172_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block172Head + surrogateDiagTailX0RatChunk000Sub001Block172Mid + surrogateDiagTailX0RatChunk000Sub001Block172Tail =
      surrogateDiagTailX0RatChunk000Sub001Block172 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block172Head surrogateDiagTailX0RatChunk000Sub001Block172Mid surrogateDiagTailX0RatChunk000Sub001Block172Tail surrogateDiagTailX0RatChunk000Sub001Block172
  ring

def SurrogateDiagonalTailChunk000Sub001Block172HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block172HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block172Head

def SurrogateDiagonalTailChunk000Sub001Block172MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block172MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block172Mid

def SurrogateDiagonalTailChunk000Sub001Block172TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block172TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block172Tail

theorem surrogateDiagonalTailChunk000Sub001Block172_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block172HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block172MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block172TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block172Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block172 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block172HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block172MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block172TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block172Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block172_eq_head_add_mid_add_tail

/-- Block 173 covers tail-support indices [9325,9350) and q from 15393 to 15430. -/

def TailChunk000Sub001Block173Part000SupportExplicit : Finset ℕ :=
  ([15393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part000 : ℚ :=
  (1577715393775 : ℚ) / 14886622218413703168

def SurrogateDiagonalTailChunk000Sub001Block173Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15393
    = surrogateDiagTailX0RatChunk000Sub001Block173Part000

theorem surrogateDiagonalTailChunk000Sub001Block173Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part000] using hcert

def TailChunk000Sub001Block173Part001SupportExplicit : Finset ℕ :=
  ([15394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part001 : ℚ :=
  (197796896875 : ℚ) / 433941838459569216

def SurrogateDiagonalTailChunk000Sub001Block173Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15394
    = surrogateDiagTailX0RatChunk000Sub001Block173Part001

theorem surrogateDiagonalTailChunk000Sub001Block173Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part001] using hcert

def TailChunk000Sub001Block173Part002SupportExplicit : Finset ℕ :=
  ([15395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part002 : ℚ :=
  (395091283075 : ℚ) / 19152260115751213056

def SurrogateDiagonalTailChunk000Sub001Block173Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15395
    = surrogateDiagTailX0RatChunk000Sub001Block173Part002

theorem surrogateDiagonalTailChunk000Sub001Block173Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part002] using hcert

def TailChunk000Sub001Block173Part003SupportExplicit : Finset ℕ :=
  ([15397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part003 : ℚ :=
  (81208766725 : ℚ) / 131241545234089771008

def SurrogateDiagonalTailChunk000Sub001Block173Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15397
    = surrogateDiagTailX0RatChunk000Sub001Block173Part003

theorem surrogateDiagonalTailChunk000Sub001Block173Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part003] using hcert

def TailChunk000Sub001Block173Part004SupportExplicit : Finset ℕ :=
  ([15398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part004 : ℚ :=
  (926165640625 : ℚ) / 2195222243353349202

def SurrogateDiagonalTailChunk000Sub001Block173Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15398
    = surrogateDiagTailX0RatChunk000Sub001Block173Part004

theorem surrogateDiagonalTailChunk000Sub001Block173Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part004] using hcert

def TailChunk000Sub001Block173Part005SupportExplicit : Finset ℕ :=
  ([15401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block173Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15401
    = surrogateDiagTailX0RatChunk000Sub001Block173Part005

theorem surrogateDiagonalTailChunk000Sub001Block173Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part005] using hcert

def TailChunk000Sub001Block173Part006SupportExplicit : Finset ℕ :=
  ([15402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part006 : ℚ :=
  (37919811653 : ℚ) / 26547388416000000

def SurrogateDiagonalTailChunk000Sub001Block173Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15402
    = surrogateDiagTailX0RatChunk000Sub001Block173Part006

theorem surrogateDiagonalTailChunk000Sub001Block173Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part006] using hcert

def TailChunk000Sub001Block173Part007SupportExplicit : Finset ℕ :=
  ([15403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part007 : ℚ :=
  (1763812523 : ℚ) / 2613749839806873600

def SurrogateDiagonalTailChunk000Sub001Block173Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15403
    = surrogateDiagTailX0RatChunk000Sub001Block173Part007

theorem surrogateDiagonalTailChunk000Sub001Block173Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part007] using hcert

def TailChunk000Sub001Block173Part008SupportExplicit : Finset ℕ :=
  ([15405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part008 : ℚ :=
  (1487890082725 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk000Sub001Block173Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15405
    = surrogateDiagTailX0RatChunk000Sub001Block173Part008

theorem surrogateDiagonalTailChunk000Sub001Block173Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part008] using hcert

def TailChunk000Sub001Block173Part009SupportExplicit : Finset ℕ :=
  ([15406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part009 : ℚ :=
  (927128265625 : ℚ) / 2199788486727410802

def SurrogateDiagonalTailChunk000Sub001Block173Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15406
    = surrogateDiagTailX0RatChunk000Sub001Block173Part009

theorem surrogateDiagonalTailChunk000Sub001Block173Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part009] using hcert

def TailChunk000Sub001Block173Part010SupportExplicit : Finset ℕ :=
  ([15407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part010 : ℚ :=
  (29407197691 : ℚ) / 2520977854752000000

def SurrogateDiagonalTailChunk000Sub001Block173Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15407
    = surrogateDiagTailX0RatChunk000Sub001Block173Part010

theorem surrogateDiagonalTailChunk000Sub001Block173Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part010] using hcert

def TailChunk000Sub001Block173Part011SupportExplicit : Finset ℕ :=
  ([15409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part011 : ℚ :=
  (201131075 : ℚ) / 90395527164254784

def SurrogateDiagonalTailChunk000Sub001Block173Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15409
    = surrogateDiagTailX0RatChunk000Sub001Block173Part011

theorem surrogateDiagonalTailChunk000Sub001Block173Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part011] using hcert

def TailChunk000Sub001Block173Part012SupportExplicit : Finset ℕ :=
  ([15410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part012 : ℚ :=
  (1238080594925 : ℚ) / 1422667118581530624

def SurrogateDiagonalTailChunk000Sub001Block173Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15410
    = surrogateDiagTailX0RatChunk000Sub001Block173Part012

theorem surrogateDiagonalTailChunk000Sub001Block173Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part012] using hcert

def TailChunk000Sub001Block173Part013SupportExplicit : Finset ℕ :=
  ([15411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part013 : ℚ :=
  (33240142469 : ℚ) / 377329277453337600

def SurrogateDiagonalTailChunk000Sub001Block173Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15411
    = surrogateDiagTailX0RatChunk000Sub001Block173Part013

theorem surrogateDiagonalTailChunk000Sub001Block173Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part013] using hcert

def TailChunk000Sub001Block173Part014SupportExplicit : Finset ℕ :=
  ([15413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block173Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15413
    = surrogateDiagTailX0RatChunk000Sub001Block173Part014

theorem surrogateDiagonalTailChunk000Sub001Block173Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part014] using hcert

def TailChunk000Sub001Block173Part015SupportExplicit : Finset ℕ :=
  ([15414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part015 : ℚ :=
  (5856803825 : ℚ) / 3230603780037696

def SurrogateDiagonalTailChunk000Sub001Block173Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15414
    = surrogateDiagTailX0RatChunk000Sub001Block173Part015

theorem surrogateDiagonalTailChunk000Sub001Block173Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part015] using hcert

def TailChunk000Sub001Block173Part016SupportExplicit : Finset ℕ :=
  ([15415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part016 : ℚ :=
  (198307017375 : ℚ) / 19252011259669682176

def SurrogateDiagonalTailChunk000Sub001Block173Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15415
    = surrogateDiagTailX0RatChunk000Sub001Block173Part016

theorem surrogateDiagonalTailChunk000Sub001Block173Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part016] using hcert

def TailChunk000Sub001Block173Part017SupportExplicit : Finset ℕ :=
  ([15418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part017 : ℚ :=
  (275983393175 : ℚ) / 530710186891935744

def SurrogateDiagonalTailChunk000Sub001Block173Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15418
    = surrogateDiagTailX0RatChunk000Sub001Block173Part017

theorem surrogateDiagonalTailChunk000Sub001Block173Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part017] using hcert

def TailChunk000Sub001Block173Part018SupportExplicit : Finset ℕ :=
  ([15419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part018 : ℚ :=
  (261304689025 : ℚ) / 110412839853060784128

def SurrogateDiagonalTailChunk000Sub001Block173Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15419
    = surrogateDiagTailX0RatChunk000Sub001Block173Part018

theorem surrogateDiagonalTailChunk000Sub001Block173Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part018] using hcert

def TailChunk000Sub001Block173Part019SupportExplicit : Finset ℕ :=
  ([15421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part019 : ℚ :=
  (16864105825 : ℚ) / 1410936144627724992

def SurrogateDiagonalTailChunk000Sub001Block173Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15421
    = surrogateDiagTailX0RatChunk000Sub001Block173Part019

theorem surrogateDiagonalTailChunk000Sub001Block173Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part019] using hcert

def TailChunk000Sub001Block173Part020SupportExplicit : Finset ℕ :=
  ([15422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part020 : ℚ :=
  (12999692497 : ℚ) / 24014802000000000

def SurrogateDiagonalTailChunk000Sub001Block173Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15422
    = surrogateDiagTailX0RatChunk000Sub001Block173Part020

theorem surrogateDiagonalTailChunk000Sub001Block173Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part020] using hcert

def TailChunk000Sub001Block173Part021SupportExplicit : Finset ℕ :=
  ([15423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part021 : ℚ :=
  (274829644075 : ℚ) / 4140891944546992128

def SurrogateDiagonalTailChunk000Sub001Block173Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15423
    = surrogateDiagTailX0RatChunk000Sub001Block173Part021

theorem surrogateDiagonalTailChunk000Sub001Block173Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part021] using hcert

def TailChunk000Sub001Block173Part022SupportExplicit : Finset ℕ :=
  ([15427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block173Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15427
    = surrogateDiagTailX0RatChunk000Sub001Block173Part022

theorem surrogateDiagonalTailChunk000Sub001Block173Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part022] using hcert

def TailChunk000Sub001Block173Part023SupportExplicit : Finset ℕ :=
  ([15429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part023 : ℚ :=
  (51545744525 : ℚ) / 761593470347142144

def SurrogateDiagonalTailChunk000Sub001Block173Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15429
    = surrogateDiagTailX0RatChunk000Sub001Block173Part023

theorem surrogateDiagonalTailChunk000Sub001Block173Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part023] using hcert

def TailChunk000Sub001Block173Part024SupportExplicit : Finset ℕ :=
  ([15430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block173Part024 : ℚ :=
  (2676650887825 : ℚ) / 3619131130895321088

def SurrogateDiagonalTailChunk000Sub001Block173Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15430
    = surrogateDiagTailX0RatChunk000Sub001Block173Part024

theorem surrogateDiagonalTailChunk000Sub001Block173Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block173Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block173Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block173Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block173Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block173Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block173Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block173HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block173Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block173Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block173Part000
    + surrogateDiagTailX0RatChunk000Sub001Block173Part001
    + surrogateDiagTailX0RatChunk000Sub001Block173Part002
    + surrogateDiagTailX0RatChunk000Sub001Block173Part003
    + surrogateDiagTailX0RatChunk000Sub001Block173Part004
    + surrogateDiagTailX0RatChunk000Sub001Block173Part005
    + surrogateDiagTailX0RatChunk000Sub001Block173Part006
    + surrogateDiagTailX0RatChunk000Sub001Block173Part007
    + surrogateDiagTailX0RatChunk000Sub001Block173Part008
    + surrogateDiagTailX0RatChunk000Sub001Block173Part009

def surrogateDiagonalTailChunk000Sub001Block173MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block173Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block173Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block173Part010
    + surrogateDiagTailX0RatChunk000Sub001Block173Part011
    + surrogateDiagTailX0RatChunk000Sub001Block173Part012
    + surrogateDiagTailX0RatChunk000Sub001Block173Part013
    + surrogateDiagTailX0RatChunk000Sub001Block173Part014
    + surrogateDiagTailX0RatChunk000Sub001Block173Part015
    + surrogateDiagTailX0RatChunk000Sub001Block173Part016
    + surrogateDiagTailX0RatChunk000Sub001Block173Part017
    + surrogateDiagTailX0RatChunk000Sub001Block173Part018
    + surrogateDiagTailX0RatChunk000Sub001Block173Part019

def surrogateDiagonalTailChunk000Sub001Block173TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block173Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block173Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block173Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block173Part020
    + surrogateDiagTailX0RatChunk000Sub001Block173Part021
    + surrogateDiagTailX0RatChunk000Sub001Block173Part022
    + surrogateDiagTailX0RatChunk000Sub001Block173Part023
    + surrogateDiagTailX0RatChunk000Sub001Block173Part024

def surrogateDiagonalTailChunk000Sub001Block173Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block173HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block173MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block173TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block173 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block173Part000
    + surrogateDiagTailX0RatChunk000Sub001Block173Part001
    + surrogateDiagTailX0RatChunk000Sub001Block173Part002
    + surrogateDiagTailX0RatChunk000Sub001Block173Part003
    + surrogateDiagTailX0RatChunk000Sub001Block173Part004
    + surrogateDiagTailX0RatChunk000Sub001Block173Part005
    + surrogateDiagTailX0RatChunk000Sub001Block173Part006
    + surrogateDiagTailX0RatChunk000Sub001Block173Part007
    + surrogateDiagTailX0RatChunk000Sub001Block173Part008
    + surrogateDiagTailX0RatChunk000Sub001Block173Part009
    + surrogateDiagTailX0RatChunk000Sub001Block173Part010
    + surrogateDiagTailX0RatChunk000Sub001Block173Part011
    + surrogateDiagTailX0RatChunk000Sub001Block173Part012
    + surrogateDiagTailX0RatChunk000Sub001Block173Part013
    + surrogateDiagTailX0RatChunk000Sub001Block173Part014
    + surrogateDiagTailX0RatChunk000Sub001Block173Part015
    + surrogateDiagTailX0RatChunk000Sub001Block173Part016
    + surrogateDiagTailX0RatChunk000Sub001Block173Part017
    + surrogateDiagTailX0RatChunk000Sub001Block173Part018
    + surrogateDiagTailX0RatChunk000Sub001Block173Part019
    + surrogateDiagTailX0RatChunk000Sub001Block173Part020
    + surrogateDiagTailX0RatChunk000Sub001Block173Part021
    + surrogateDiagTailX0RatChunk000Sub001Block173Part022
    + surrogateDiagTailX0RatChunk000Sub001Block173Part023
    + surrogateDiagTailX0RatChunk000Sub001Block173Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block173_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block173Head + surrogateDiagTailX0RatChunk000Sub001Block173Mid + surrogateDiagTailX0RatChunk000Sub001Block173Tail =
      surrogateDiagTailX0RatChunk000Sub001Block173 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block173Head surrogateDiagTailX0RatChunk000Sub001Block173Mid surrogateDiagTailX0RatChunk000Sub001Block173Tail surrogateDiagTailX0RatChunk000Sub001Block173
  ring

def SurrogateDiagonalTailChunk000Sub001Block173HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block173HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block173Head

def SurrogateDiagonalTailChunk000Sub001Block173MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block173MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block173Mid

def SurrogateDiagonalTailChunk000Sub001Block173TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block173TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block173Tail

theorem surrogateDiagonalTailChunk000Sub001Block173_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block173HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block173MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block173TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block173Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block173 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block173HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block173MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block173TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block173Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block173_eq_head_add_mid_add_tail

/-- Block 174 covers tail-support indices [9350,9375) and q from 15431 to 15470. -/

def TailChunk000Sub001Block174Part000SupportExplicit : Finset ℕ :=
  ([15431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part000 : ℚ :=
  (59198510275 : ℚ) / 17097765203613109248

def SurrogateDiagonalTailChunk000Sub001Block174Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15431
    = surrogateDiagTailX0RatChunk000Sub001Block174Part000

theorem surrogateDiagonalTailChunk000Sub001Block174Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part000] using hcert

def TailChunk000Sub001Block174Part001SupportExplicit : Finset ℕ :=
  ([15433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part001 : ℚ :=
  (3797518951 : ℚ) / 506094158592000000

def SurrogateDiagonalTailChunk000Sub001Block174Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15433
    = surrogateDiagTailX0RatChunk000Sub001Block174Part001

theorem surrogateDiagonalTailChunk000Sub001Block174Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part001] using hcert

def TailChunk000Sub001Block174Part002SupportExplicit : Finset ℕ :=
  ([15434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part002 : ℚ :=
  (930501390625 : ℚ) / 2215826456464917792

def SurrogateDiagonalTailChunk000Sub001Block174Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15434
    = surrogateDiagTailX0RatChunk000Sub001Block174Part002

theorem surrogateDiagonalTailChunk000Sub001Block174Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part002] using hcert

def TailChunk000Sub001Block174Part003SupportExplicit : Finset ℕ :=
  ([15437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part003 : ℚ :=
  (125052655225 : ℚ) / 127807437378799559808

def SurrogateDiagonalTailChunk000Sub001Block174Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15437
    = surrogateDiagTailX0RatChunk000Sub001Block174Part003

theorem surrogateDiagonalTailChunk000Sub001Block174Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part003] using hcert

def TailChunk000Sub001Block174Part004SupportExplicit : Finset ℕ :=
  ([15438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part004 : ℚ :=
  (7832999263 : ℚ) / 5860669909201920

def SurrogateDiagonalTailChunk000Sub001Block174Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15438
    = surrogateDiagTailX0RatChunk000Sub001Block174Part004

theorem surrogateDiagonalTailChunk000Sub001Block174Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part004] using hcert

def TailChunk000Sub001Block174Part005SupportExplicit : Finset ℕ :=
  ([15439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block174Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15439
    = surrogateDiagTailX0RatChunk000Sub001Block174Part005

theorem surrogateDiagonalTailChunk000Sub001Block174Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part005] using hcert

def TailChunk000Sub001Block174Part006SupportExplicit : Finset ℕ :=
  ([15441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part006 : ℚ :=
  (827853654425 : ℚ) / 14028006982225487424

def SurrogateDiagonalTailChunk000Sub001Block174Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15441
    = surrogateDiagTailX0RatChunk000Sub001Block174Part006

theorem surrogateDiagonalTailChunk000Sub001Block174Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part006] using hcert

def TailChunk000Sub001Block174Part007SupportExplicit : Finset ℕ :=
  ([15442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part007 : ℚ :=
  (164579834975 : ℚ) / 265512965513587776

def SurrogateDiagonalTailChunk000Sub001Block174Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15442
    = surrogateDiagTailX0RatChunk000Sub001Block174Part007

theorem surrogateDiagonalTailChunk000Sub001Block174Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part007] using hcert

def TailChunk000Sub001Block174Part008SupportExplicit : Finset ℕ :=
  ([15443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block174Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15443
    = surrogateDiagTailX0RatChunk000Sub001Block174Part008

theorem surrogateDiagonalTailChunk000Sub001Block174Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part008] using hcert

def TailChunk000Sub001Block174Part009SupportExplicit : Finset ℕ :=
  ([15445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part009 : ℚ :=
  (1192979804725 : ℚ) / 58207103818408132608

def SurrogateDiagonalTailChunk000Sub001Block174Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15445
    = surrogateDiagTailX0RatChunk000Sub001Block174Part009

theorem surrogateDiagonalTailChunk000Sub001Block174Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part009] using hcert

def TailChunk000Sub001Block174Part010SupportExplicit : Finset ℕ :=
  ([15446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part010 : ℚ :=
  (931948890625 : ℚ) / 2222726650409204082

def SurrogateDiagonalTailChunk000Sub001Block174Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15446
    = surrogateDiagTailX0RatChunk000Sub001Block174Part010

theorem surrogateDiagonalTailChunk000Sub001Block174Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part010] using hcert

def TailChunk000Sub001Block174Part011SupportExplicit : Finset ℕ :=
  ([15447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part011 : ℚ :=
  (6587723137 : ℚ) / 89279533001733120

def SurrogateDiagonalTailChunk000Sub001Block174Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15447
    = surrogateDiagTailX0RatChunk000Sub001Block174Part011

theorem surrogateDiagonalTailChunk000Sub001Block174Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part011] using hcert

def TailChunk000Sub001Block174Part012SupportExplicit : Finset ℕ :=
  ([15449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part012 : ℚ :=
  (305028818375 : ℚ) / 38372835966782359104

def SurrogateDiagonalTailChunk000Sub001Block174Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15449
    = surrogateDiagTailX0RatChunk000Sub001Block174Part012

theorem surrogateDiagonalTailChunk000Sub001Block174Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part012] using hcert

def TailChunk000Sub001Block174Part013SupportExplicit : Finset ℕ :=
  ([15451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block174Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15451
    = surrogateDiagTailX0RatChunk000Sub001Block174Part013

theorem surrogateDiagonalTailChunk000Sub001Block174Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part013] using hcert

def TailChunk000Sub001Block174Part014SupportExplicit : Finset ℕ :=
  ([15454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part014 : ℚ :=
  (932914515625 : ℚ) / 2227335724342864722

def SurrogateDiagonalTailChunk000Sub001Block174Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15454
    = surrogateDiagTailX0RatChunk000Sub001Block174Part014

theorem surrogateDiagonalTailChunk000Sub001Block174Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part014] using hcert

def TailChunk000Sub001Block174Part015SupportExplicit : Finset ℕ :=
  ([15455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part015 : ℚ :=
  (682300067 : ℚ) / 19672925798400000

def SurrogateDiagonalTailChunk000Sub001Block174Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15455
    = surrogateDiagTailX0RatChunk000Sub001Block174Part015

theorem surrogateDiagonalTailChunk000Sub001Block174Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part015] using hcert

def TailChunk000Sub001Block174Part016SupportExplicit : Finset ℕ :=
  ([15457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part016 : ℚ :=
  (11136489947 : ℚ) / 1631751157422489600

def SurrogateDiagonalTailChunk000Sub001Block174Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15457
    = surrogateDiagTailX0RatChunk000Sub001Block174Part016

theorem surrogateDiagonalTailChunk000Sub001Block174Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part016] using hcert

def TailChunk000Sub001Block174Part017SupportExplicit : Finset ℕ :=
  ([15458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part017 : ℚ :=
  (144436024093 : ℚ) / 323275084344451200

def SurrogateDiagonalTailChunk000Sub001Block174Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15458
    = surrogateDiagTailX0RatChunk000Sub001Block174Part017

theorem surrogateDiagonalTailChunk000Sub001Block174Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part017] using hcert

def TailChunk000Sub001Block174Part018SupportExplicit : Finset ℕ :=
  ([15459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part018 : ℚ :=
  (8467189075 : ℚ) / 143811689230368768

def SurrogateDiagonalTailChunk000Sub001Block174Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15459
    = surrogateDiagTailX0RatChunk000Sub001Block174Part018

theorem surrogateDiagonalTailChunk000Sub001Block174Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part018] using hcert

def TailChunk000Sub001Block174Part019SupportExplicit : Finset ℕ :=
  ([15461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block174Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15461
    = surrogateDiagTailX0RatChunk000Sub001Block174Part019

theorem surrogateDiagonalTailChunk000Sub001Block174Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part019] using hcert

def TailChunk000Sub001Block174Part020SupportExplicit : Finset ℕ :=
  ([15465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part020 : ℚ :=
  (345265901 : ℚ) / 2305503051288576

def SurrogateDiagonalTailChunk000Sub001Block174Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15465
    = surrogateDiagTailX0RatChunk000Sub001Block174Part020

theorem surrogateDiagonalTailChunk000Sub001Block174Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part020] using hcert

def TailChunk000Sub001Block174Part021SupportExplicit : Finset ℕ :=
  ([15466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part021 : ℚ :=
  (117404093737 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub001Block174Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15466
    = surrogateDiagTailX0RatChunk000Sub001Block174Part021

theorem surrogateDiagonalTailChunk000Sub001Block174Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part021] using hcert

def TailChunk000Sub001Block174Part022SupportExplicit : Finset ℕ :=
  ([15467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block174Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15467
    = surrogateDiagTailX0RatChunk000Sub001Block174Part022

theorem surrogateDiagonalTailChunk000Sub001Block174Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part022] using hcert

def TailChunk000Sub001Block174Part023SupportExplicit : Finset ℕ :=
  ([15469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part023 : ℚ :=
  (16205777 : ℚ) / 12303657042560640

def SurrogateDiagonalTailChunk000Sub001Block174Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15469
    = surrogateDiagTailX0RatChunk000Sub001Block174Part023

theorem surrogateDiagonalTailChunk000Sub001Block174Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part023] using hcert

def TailChunk000Sub001Block174Part024SupportExplicit : Finset ℕ :=
  ([15470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block174Part024 : ℚ :=
  (103259268275 : ℚ) / 62633147300315136

def SurrogateDiagonalTailChunk000Sub001Block174Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15470
    = surrogateDiagTailX0RatChunk000Sub001Block174Part024

theorem surrogateDiagonalTailChunk000Sub001Block174Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block174Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block174Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block174Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block174Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block174Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block174Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block174HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block174Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block174Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block174Part000
    + surrogateDiagTailX0RatChunk000Sub001Block174Part001
    + surrogateDiagTailX0RatChunk000Sub001Block174Part002
    + surrogateDiagTailX0RatChunk000Sub001Block174Part003
    + surrogateDiagTailX0RatChunk000Sub001Block174Part004
    + surrogateDiagTailX0RatChunk000Sub001Block174Part005
    + surrogateDiagTailX0RatChunk000Sub001Block174Part006
    + surrogateDiagTailX0RatChunk000Sub001Block174Part007
    + surrogateDiagTailX0RatChunk000Sub001Block174Part008
    + surrogateDiagTailX0RatChunk000Sub001Block174Part009

def surrogateDiagonalTailChunk000Sub001Block174MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block174Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block174Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block174Part010
    + surrogateDiagTailX0RatChunk000Sub001Block174Part011
    + surrogateDiagTailX0RatChunk000Sub001Block174Part012
    + surrogateDiagTailX0RatChunk000Sub001Block174Part013
    + surrogateDiagTailX0RatChunk000Sub001Block174Part014
    + surrogateDiagTailX0RatChunk000Sub001Block174Part015
    + surrogateDiagTailX0RatChunk000Sub001Block174Part016
    + surrogateDiagTailX0RatChunk000Sub001Block174Part017
    + surrogateDiagTailX0RatChunk000Sub001Block174Part018
    + surrogateDiagTailX0RatChunk000Sub001Block174Part019

def surrogateDiagonalTailChunk000Sub001Block174TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block174Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block174Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block174Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block174Part020
    + surrogateDiagTailX0RatChunk000Sub001Block174Part021
    + surrogateDiagTailX0RatChunk000Sub001Block174Part022
    + surrogateDiagTailX0RatChunk000Sub001Block174Part023
    + surrogateDiagTailX0RatChunk000Sub001Block174Part024

def surrogateDiagonalTailChunk000Sub001Block174Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block174HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block174MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block174TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block174 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block174Part000
    + surrogateDiagTailX0RatChunk000Sub001Block174Part001
    + surrogateDiagTailX0RatChunk000Sub001Block174Part002
    + surrogateDiagTailX0RatChunk000Sub001Block174Part003
    + surrogateDiagTailX0RatChunk000Sub001Block174Part004
    + surrogateDiagTailX0RatChunk000Sub001Block174Part005
    + surrogateDiagTailX0RatChunk000Sub001Block174Part006
    + surrogateDiagTailX0RatChunk000Sub001Block174Part007
    + surrogateDiagTailX0RatChunk000Sub001Block174Part008
    + surrogateDiagTailX0RatChunk000Sub001Block174Part009
    + surrogateDiagTailX0RatChunk000Sub001Block174Part010
    + surrogateDiagTailX0RatChunk000Sub001Block174Part011
    + surrogateDiagTailX0RatChunk000Sub001Block174Part012
    + surrogateDiagTailX0RatChunk000Sub001Block174Part013
    + surrogateDiagTailX0RatChunk000Sub001Block174Part014
    + surrogateDiagTailX0RatChunk000Sub001Block174Part015
    + surrogateDiagTailX0RatChunk000Sub001Block174Part016
    + surrogateDiagTailX0RatChunk000Sub001Block174Part017
    + surrogateDiagTailX0RatChunk000Sub001Block174Part018
    + surrogateDiagTailX0RatChunk000Sub001Block174Part019
    + surrogateDiagTailX0RatChunk000Sub001Block174Part020
    + surrogateDiagTailX0RatChunk000Sub001Block174Part021
    + surrogateDiagTailX0RatChunk000Sub001Block174Part022
    + surrogateDiagTailX0RatChunk000Sub001Block174Part023
    + surrogateDiagTailX0RatChunk000Sub001Block174Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block174_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block174Head + surrogateDiagTailX0RatChunk000Sub001Block174Mid + surrogateDiagTailX0RatChunk000Sub001Block174Tail =
      surrogateDiagTailX0RatChunk000Sub001Block174 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block174Head surrogateDiagTailX0RatChunk000Sub001Block174Mid surrogateDiagTailX0RatChunk000Sub001Block174Tail surrogateDiagTailX0RatChunk000Sub001Block174
  ring

def SurrogateDiagonalTailChunk000Sub001Block174HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block174HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block174Head

def SurrogateDiagonalTailChunk000Sub001Block174MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block174MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block174Mid

def SurrogateDiagonalTailChunk000Sub001Block174TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block174TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block174Tail

theorem surrogateDiagonalTailChunk000Sub001Block174_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block174HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block174MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block174TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block174Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block174 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block174HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block174MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block174TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block174Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block174_eq_head_add_mid_add_tail

/-- Block 175 covers tail-support indices [9375,9400) and q from 15473 to 15510. -/

def TailChunk000Sub001Block175Part000SupportExplicit : Finset ℕ :=
  ([15473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block175Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15473
    = surrogateDiagTailX0RatChunk000Sub001Block175Part000

theorem surrogateDiagonalTailChunk000Sub001Block175Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part000] using hcert

def TailChunk000Sub001Block175Part001SupportExplicit : Finset ℕ :=
  ([15474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part001 : ℚ :=
  (32466537925 : ℚ) / 27612041638476882

def SurrogateDiagonalTailChunk000Sub001Block175Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15474
    = surrogateDiagTailX0RatChunk000Sub001Block175Part001

theorem surrogateDiagonalTailChunk000Sub001Block175Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part001] using hcert

def TailChunk000Sub001Block175Part002SupportExplicit : Finset ℕ :=
  ([15477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part002 : ℚ :=
  (12425055101 : ℚ) / 78707763544227840

def SurrogateDiagonalTailChunk000Sub001Block175Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15477
    = surrogateDiagTailX0RatChunk000Sub001Block175Part002

theorem surrogateDiagonalTailChunk000Sub001Block175Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part002] using hcert

def TailChunk000Sub001Block175Part003SupportExplicit : Finset ℕ :=
  ([15478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part003 : ℚ :=
  (4145110799 : ℚ) / 9334820856453120

def SurrogateDiagonalTailChunk000Sub001Block175Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15478
    = surrogateDiagTailX0RatChunk000Sub001Block175Part003

theorem surrogateDiagonalTailChunk000Sub001Block175Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part003] using hcert

def TailChunk000Sub001Block175Part004SupportExplicit : Finset ℕ :=
  ([15479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part004 : ℚ :=
  (58085070625 : ℚ) / 29863085869778337792

def SurrogateDiagonalTailChunk000Sub001Block175Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15479
    = surrogateDiagTailX0RatChunk000Sub001Block175Part004

theorem surrogateDiagonalTailChunk000Sub001Block175Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part004] using hcert

def TailChunk000Sub001Block175Part005SupportExplicit : Finset ℕ :=
  ([15481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part005 : ℚ :=
  (78043191775 : ℚ) / 134602951525020991488

def SurrogateDiagonalTailChunk000Sub001Block175Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15481
    = surrogateDiagTailX0RatChunk000Sub001Block175Part005

theorem surrogateDiagonalTailChunk000Sub001Block175Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part005] using hcert

def TailChunk000Sub001Block175Part006SupportExplicit : Finset ℕ :=
  ([15482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part006 : ℚ :=
  (1498077025 : ℚ) / 3589638321867552

def SurrogateDiagonalTailChunk000Sub001Block175Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15482
    = surrogateDiagTailX0RatChunk000Sub001Block175Part006

theorem surrogateDiagonalTailChunk000Sub001Block175Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part006] using hcert

def TailChunk000Sub001Block175Part007SupportExplicit : Finset ℕ :=
  ([15483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part007 : ℚ :=
  (1683353724625 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk000Sub001Block175Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15483
    = surrogateDiagTailX0RatChunk000Sub001Block175Part007

theorem surrogateDiagonalTailChunk000Sub001Block175Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part007] using hcert

def TailChunk000Sub001Block175Part008SupportExplicit : Finset ℕ :=
  ([15485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part008 : ℚ :=
  (426713643275 : ℚ) / 15427503302699483136

def SurrogateDiagonalTailChunk000Sub001Block175Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15485
    = surrogateDiagTailX0RatChunk000Sub001Block175Part008

theorem surrogateDiagonalTailChunk000Sub001Block175Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part008] using hcert

def TailChunk000Sub001Block175Part009SupportExplicit : Finset ℕ :=
  ([15486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part009 : ℚ :=
  (655834387575 : ℚ) / 491573429955198976

def SurrogateDiagonalTailChunk000Sub001Block175Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15486
    = surrogateDiagTailX0RatChunk000Sub001Block175Part009

theorem surrogateDiagonalTailChunk000Sub001Block175Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part009] using hcert

def TailChunk000Sub001Block175Part010SupportExplicit : Finset ℕ :=
  ([15487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part010 : ℚ :=
  (2101502433 : ℚ) / 749171244970803200

def SurrogateDiagonalTailChunk000Sub001Block175Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15487
    = surrogateDiagTailX0RatChunk000Sub001Block175Part010

theorem surrogateDiagonalTailChunk000Sub001Block175Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part010] using hcert

def TailChunk000Sub001Block175Part011SupportExplicit : Finset ℕ :=
  ([15490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part011 : ℚ :=
  (474566724475 : ℚ) / 612631606932062208

def SurrogateDiagonalTailChunk000Sub001Block175Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15490
    = surrogateDiagTailX0RatChunk000Sub001Block175Part011

theorem surrogateDiagonalTailChunk000Sub001Block175Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part011] using hcert

def TailChunk000Sub001Block175Part012SupportExplicit : Finset ℕ :=
  ([15491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part012 : ℚ :=
  (1041876025 : ℚ) / 87963756124898304

def SurrogateDiagonalTailChunk000Sub001Block175Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15491
    = surrogateDiagTailX0RatChunk000Sub001Block175Part012

theorem surrogateDiagonalTailChunk000Sub001Block175Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part012] using hcert

def TailChunk000Sub001Block175Part013SupportExplicit : Finset ℕ :=
  ([15493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block175Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15493
    = surrogateDiagTailX0RatChunk000Sub001Block175Part013

theorem surrogateDiagonalTailChunk000Sub001Block175Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part013] using hcert

def TailChunk000Sub001Block175Part014SupportExplicit : Finset ℕ :=
  ([15494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part014 : ℚ :=
  (403218191 : ℚ) / 907552027710720

def SurrogateDiagonalTailChunk000Sub001Block175Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15494
    = surrogateDiagTailX0RatChunk000Sub001Block175Part014

theorem surrogateDiagonalTailChunk000Sub001Block175Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part014] using hcert

def TailChunk000Sub001Block175Part015SupportExplicit : Finset ℕ :=
  ([15495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part015 : ℚ :=
  (122248978775 : ℚ) / 968109206016098304

def SurrogateDiagonalTailChunk000Sub001Block175Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15495
    = surrogateDiagTailX0RatChunk000Sub001Block175Part015

theorem surrogateDiagonalTailChunk000Sub001Block175Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part015] using hcert

def TailChunk000Sub001Block175Part016SupportExplicit : Finset ℕ :=
  ([15497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block175Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15497
    = surrogateDiagTailX0RatChunk000Sub001Block175Part016

theorem surrogateDiagonalTailChunk000Sub001Block175Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part016] using hcert

def TailChunk000Sub001Block175Part017SupportExplicit : Finset ℕ :=
  ([15499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part017 : ℚ :=
  (6645943383 : ℚ) / 1310316514666086400

def SurrogateDiagonalTailChunk000Sub001Block175Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15499
    = surrogateDiagTailX0RatChunk000Sub001Block175Part017

theorem surrogateDiagonalTailChunk000Sub001Block175Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part017] using hcert

def TailChunk000Sub001Block175Part018SupportExplicit : Finset ℕ :=
  ([15501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part018 : ℚ :=
  (119185522025 : ℚ) / 2035337401091961792

def SurrogateDiagonalTailChunk000Sub001Block175Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15501
    = surrogateDiagTailX0RatChunk000Sub001Block175Part018

theorem surrogateDiagonalTailChunk000Sub001Block175Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part018] using hcert

def TailChunk000Sub001Block175Part019SupportExplicit : Finset ℕ :=
  ([15502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part019 : ℚ :=
  (391259193175 : ℚ) / 829530163049398272

def SurrogateDiagonalTailChunk000Sub001Block175Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15502
    = surrogateDiagTailX0RatChunk000Sub001Block175Part019

theorem surrogateDiagonalTailChunk000Sub001Block175Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part019] using hcert

def TailChunk000Sub001Block175Part020SupportExplicit : Finset ℕ :=
  ([15503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part020 : ℚ :=
  (15777175025 : ℚ) / 14246214517843494912

def SurrogateDiagonalTailChunk000Sub001Block175Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15503
    = surrogateDiagTailX0RatChunk000Sub001Block175Part020

theorem surrogateDiagonalTailChunk000Sub001Block175Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part020] using hcert

def TailChunk000Sub001Block175Part021SupportExplicit : Finset ℕ :=
  ([15505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part021 : ℚ :=
  (51976549825 : ℚ) / 1759091370140123136

def SurrogateDiagonalTailChunk000Sub001Block175Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15505
    = surrogateDiagTailX0RatChunk000Sub001Block175Part021

theorem surrogateDiagonalTailChunk000Sub001Block175Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part021] using hcert

def TailChunk000Sub001Block175Part022SupportExplicit : Finset ℕ :=
  ([15506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part022 : ℚ :=
  (939203265625 : ℚ) / 2257469668026634752

def SurrogateDiagonalTailChunk000Sub001Block175Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15506
    = surrogateDiagTailX0RatChunk000Sub001Block175Part022

theorem surrogateDiagonalTailChunk000Sub001Block175Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part022] using hcert

def TailChunk000Sub001Block175Part023SupportExplicit : Finset ℕ :=
  ([15509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part023 : ℚ :=
  (59792652775 : ℚ) / 17446391516712665088

def SurrogateDiagonalTailChunk000Sub001Block175Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15509
    = surrogateDiagTailX0RatChunk000Sub001Block175Part023

theorem surrogateDiagonalTailChunk000Sub001Block175Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part023] using hcert

def TailChunk000Sub001Block175Part024SupportExplicit : Finset ℕ :=
  ([15510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block175Part024 : ℚ :=
  (5413370083 : ℚ) / 1834332770795520

def SurrogateDiagonalTailChunk000Sub001Block175Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15510
    = surrogateDiagTailX0RatChunk000Sub001Block175Part024

theorem surrogateDiagonalTailChunk000Sub001Block175Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block175Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block175Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block175Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block175Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block175Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block175Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block175HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block175Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block175Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block175Part000
    + surrogateDiagTailX0RatChunk000Sub001Block175Part001
    + surrogateDiagTailX0RatChunk000Sub001Block175Part002
    + surrogateDiagTailX0RatChunk000Sub001Block175Part003
    + surrogateDiagTailX0RatChunk000Sub001Block175Part004
    + surrogateDiagTailX0RatChunk000Sub001Block175Part005
    + surrogateDiagTailX0RatChunk000Sub001Block175Part006
    + surrogateDiagTailX0RatChunk000Sub001Block175Part007
    + surrogateDiagTailX0RatChunk000Sub001Block175Part008
    + surrogateDiagTailX0RatChunk000Sub001Block175Part009

def surrogateDiagonalTailChunk000Sub001Block175MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block175Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block175Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block175Part010
    + surrogateDiagTailX0RatChunk000Sub001Block175Part011
    + surrogateDiagTailX0RatChunk000Sub001Block175Part012
    + surrogateDiagTailX0RatChunk000Sub001Block175Part013
    + surrogateDiagTailX0RatChunk000Sub001Block175Part014
    + surrogateDiagTailX0RatChunk000Sub001Block175Part015
    + surrogateDiagTailX0RatChunk000Sub001Block175Part016
    + surrogateDiagTailX0RatChunk000Sub001Block175Part017
    + surrogateDiagTailX0RatChunk000Sub001Block175Part018
    + surrogateDiagTailX0RatChunk000Sub001Block175Part019

def surrogateDiagonalTailChunk000Sub001Block175TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block175Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block175Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block175Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block175Part020
    + surrogateDiagTailX0RatChunk000Sub001Block175Part021
    + surrogateDiagTailX0RatChunk000Sub001Block175Part022
    + surrogateDiagTailX0RatChunk000Sub001Block175Part023
    + surrogateDiagTailX0RatChunk000Sub001Block175Part024

def surrogateDiagonalTailChunk000Sub001Block175Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block175HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block175MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block175TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block175 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block175Part000
    + surrogateDiagTailX0RatChunk000Sub001Block175Part001
    + surrogateDiagTailX0RatChunk000Sub001Block175Part002
    + surrogateDiagTailX0RatChunk000Sub001Block175Part003
    + surrogateDiagTailX0RatChunk000Sub001Block175Part004
    + surrogateDiagTailX0RatChunk000Sub001Block175Part005
    + surrogateDiagTailX0RatChunk000Sub001Block175Part006
    + surrogateDiagTailX0RatChunk000Sub001Block175Part007
    + surrogateDiagTailX0RatChunk000Sub001Block175Part008
    + surrogateDiagTailX0RatChunk000Sub001Block175Part009
    + surrogateDiagTailX0RatChunk000Sub001Block175Part010
    + surrogateDiagTailX0RatChunk000Sub001Block175Part011
    + surrogateDiagTailX0RatChunk000Sub001Block175Part012
    + surrogateDiagTailX0RatChunk000Sub001Block175Part013
    + surrogateDiagTailX0RatChunk000Sub001Block175Part014
    + surrogateDiagTailX0RatChunk000Sub001Block175Part015
    + surrogateDiagTailX0RatChunk000Sub001Block175Part016
    + surrogateDiagTailX0RatChunk000Sub001Block175Part017
    + surrogateDiagTailX0RatChunk000Sub001Block175Part018
    + surrogateDiagTailX0RatChunk000Sub001Block175Part019
    + surrogateDiagTailX0RatChunk000Sub001Block175Part020
    + surrogateDiagTailX0RatChunk000Sub001Block175Part021
    + surrogateDiagTailX0RatChunk000Sub001Block175Part022
    + surrogateDiagTailX0RatChunk000Sub001Block175Part023
    + surrogateDiagTailX0RatChunk000Sub001Block175Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block175_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block175Head + surrogateDiagTailX0RatChunk000Sub001Block175Mid + surrogateDiagTailX0RatChunk000Sub001Block175Tail =
      surrogateDiagTailX0RatChunk000Sub001Block175 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block175Head surrogateDiagTailX0RatChunk000Sub001Block175Mid surrogateDiagTailX0RatChunk000Sub001Block175Tail surrogateDiagTailX0RatChunk000Sub001Block175
  ring

def SurrogateDiagonalTailChunk000Sub001Block175HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block175HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block175Head

def SurrogateDiagonalTailChunk000Sub001Block175MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block175MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block175Mid

def SurrogateDiagonalTailChunk000Sub001Block175TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block175TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block175Tail

theorem surrogateDiagonalTailChunk000Sub001Block175_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block175HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block175MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block175TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block175Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block175 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block175HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block175MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block175TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block175Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block175_eq_head_add_mid_add_tail

/-- Block 176 covers tail-support indices [9400,9425) and q from 15511 to 15551. -/

def TailChunk000Sub001Block176Part000SupportExplicit : Finset ℕ :=
  ([15511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block176Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15511
    = surrogateDiagTailX0RatChunk000Sub001Block176Part000

theorem surrogateDiagonalTailChunk000Sub001Block176Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part000] using hcert

def TailChunk000Sub001Block176Part001SupportExplicit : Finset ℕ :=
  ([15513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part001 : ℚ :=
  (6684725233 : ℚ) / 114332317124646720

def SurrogateDiagonalTailChunk000Sub001Block176Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15513
    = surrogateDiagTailX0RatChunk000Sub001Block176Part001

theorem surrogateDiagonalTailChunk000Sub001Block176Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part001] using hcert

def TailChunk000Sub001Block176Part002SupportExplicit : Finset ℕ :=
  ([15514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part002 : ℚ :=
  (940172640625 : ℚ) / 2262132655718490912

def SurrogateDiagonalTailChunk000Sub001Block176Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15514
    = surrogateDiagTailX0RatChunk000Sub001Block176Part002

theorem surrogateDiagonalTailChunk000Sub001Block176Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part002] using hcert

def TailChunk000Sub001Block176Part003SupportExplicit : Finset ℕ :=
  ([15515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part003 : ℚ :=
  (356139930425 : ℚ) / 24836615556269604864

def SurrogateDiagonalTailChunk000Sub001Block176Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15515
    = surrogateDiagTailX0RatChunk000Sub001Block176Part003

theorem surrogateDiagonalTailChunk000Sub001Block176Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part003] using hcert

def TailChunk000Sub001Block176Part004SupportExplicit : Finset ℕ :=
  ([15517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part004 : ℚ :=
  (6212382775 : ℚ) / 8333434298581038408

def SurrogateDiagonalTailChunk000Sub001Block176Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15517
    = surrogateDiagTailX0RatChunk000Sub001Block176Part004

theorem surrogateDiagonalTailChunk000Sub001Block176Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part004] using hcert

def TailChunk000Sub001Block176Part005SupportExplicit : Finset ℕ :=
  ([15518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part005 : ℚ :=
  (940657515625 : ℚ) / 2264466856639575762

def SurrogateDiagonalTailChunk000Sub001Block176Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15518
    = surrogateDiagTailX0RatChunk000Sub001Block176Part005

theorem surrogateDiagonalTailChunk000Sub001Block176Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part005] using hcert

def TailChunk000Sub001Block176Part006SupportExplicit : Finset ℕ :=
  ([15519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part006 : ℚ :=
  (181973295125 : ℚ) / 1708971345523279872

def SurrogateDiagonalTailChunk000Sub001Block176Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15519
    = surrogateDiagTailX0RatChunk000Sub001Block176Part006

theorem surrogateDiagonalTailChunk000Sub001Block176Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part006] using hcert

def TailChunk000Sub001Block176Part007SupportExplicit : Finset ℕ :=
  ([15521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part007 : ℚ :=
  (12930089321 : ℚ) / 1481808885684633600

def SurrogateDiagonalTailChunk000Sub001Block176Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15521
    = surrogateDiagTailX0RatChunk000Sub001Block176Part007

theorem surrogateDiagonalTailChunk000Sub001Block176Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part007] using hcert

def TailChunk000Sub001Block176Part008SupportExplicit : Finset ℕ :=
  ([15522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part008 : ℚ :=
  (3867735125 : ℚ) / 2623592118140928

def SurrogateDiagonalTailChunk000Sub001Block176Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15522
    = surrogateDiagTailX0RatChunk000Sub001Block176Part008

theorem surrogateDiagonalTailChunk000Sub001Block176Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part008] using hcert

def TailChunk000Sub001Block176Part009SupportExplicit : Finset ℕ :=
  ([15526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part009 : ℚ :=
  (3071584483375 : ℚ) / 4884171464908228608

def SurrogateDiagonalTailChunk000Sub001Block176Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15526
    = surrogateDiagTailX0RatChunk000Sub001Block176Part009

theorem surrogateDiagonalTailChunk000Sub001Block176Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part009] using hcert

def TailChunk000Sub001Block176Part010SupportExplicit : Finset ℕ :=
  ([15527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block176Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15527
    = surrogateDiagTailX0RatChunk000Sub001Block176Part010

theorem surrogateDiagonalTailChunk000Sub001Block176Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part010] using hcert

def TailChunk000Sub001Block176Part011SupportExplicit : Finset ℕ :=
  ([15529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part011 : ℚ :=
  (13332571925 : ℚ) / 16614284853928759296

def SurrogateDiagonalTailChunk000Sub001Block176Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15529
    = surrogateDiagTailX0RatChunk000Sub001Block176Part011

theorem surrogateDiagonalTailChunk000Sub001Block176Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part011] using hcert

def TailChunk000Sub001Block176Part012SupportExplicit : Finset ℕ :=
  ([15530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part012 : ℚ :=
  (1431064068575 : ℚ) / 1856964905794535424

def SurrogateDiagonalTailChunk000Sub001Block176Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15530
    = surrogateDiagTailX0RatChunk000Sub001Block176Part012

theorem surrogateDiagonalTailChunk000Sub001Block176Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part012] using hcert

def TailChunk000Sub001Block176Part013SupportExplicit : Finset ℕ :=
  ([15531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part013 : ℚ :=
  (16634984941 : ℚ) / 246073140851212800

def SurrogateDiagonalTailChunk000Sub001Block176Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15531
    = surrogateDiagTailX0RatChunk000Sub001Block176Part013

theorem surrogateDiagonalTailChunk000Sub001Block176Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part013] using hcert

def TailChunk000Sub001Block176Part014SupportExplicit : Finset ℕ :=
  ([15535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part014 : ℚ :=
  (436834489475 : ℚ) / 14196405043654557696

def SurrogateDiagonalTailChunk000Sub001Block176Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15535
    = surrogateDiagTailX0RatChunk000Sub001Block176Part014

theorem surrogateDiagonalTailChunk000Sub001Block176Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part014] using hcert

def TailChunk000Sub001Block176Part015SupportExplicit : Finset ℕ :=
  ([15537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part015 : ℚ :=
  (838177654025 : ℚ) / 14380203443912783424

def SurrogateDiagonalTailChunk000Sub001Block176Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15537
    = surrogateDiagTailX0RatChunk000Sub001Block176Part015

theorem surrogateDiagonalTailChunk000Sub001Block176Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part015] using hcert

def TailChunk000Sub001Block176Part016SupportExplicit : Finset ℕ :=
  ([15538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part016 : ℚ :=
  (144271489925 : ℚ) / 295226214891651072

def SurrogateDiagonalTailChunk000Sub001Block176Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15538
    = surrogateDiagTailX0RatChunk000Sub001Block176Part016

theorem surrogateDiagonalTailChunk000Sub001Block176Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part016] using hcert

def TailChunk000Sub001Block176Part017SupportExplicit : Finset ℕ :=
  ([15539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part017 : ℚ :=
  (5132781187 : ℚ) / 5227499679613747200

def SurrogateDiagonalTailChunk000Sub001Block176Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15539
    = surrogateDiagTailX0RatChunk000Sub001Block176Part017

theorem surrogateDiagonalTailChunk000Sub001Block176Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part017] using hcert

def TailChunk000Sub001Block176Part018SupportExplicit : Finset ℕ :=
  ([15541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block176Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15541
    = surrogateDiagTailX0RatChunk000Sub001Block176Part018

theorem surrogateDiagonalTailChunk000Sub001Block176Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part018] using hcert

def TailChunk000Sub001Block176Part019SupportExplicit : Finset ℕ :=
  ([15542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part019 : ℚ :=
  (130194603625 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub001Block176Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15542
    = surrogateDiagTailX0RatChunk000Sub001Block176Part019

theorem surrogateDiagonalTailChunk000Sub001Block176Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part019] using hcert

def TailChunk000Sub001Block176Part020SupportExplicit : Finset ℕ :=
  ([15545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part020 : ℚ :=
  (402822233575 : ℚ) / 19909924355117776896

def SurrogateDiagonalTailChunk000Sub001Block176Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15545
    = surrogateDiagTailX0RatChunk000Sub001Block176Part020

theorem surrogateDiagonalTailChunk000Sub001Block176Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part020] using hcert

def TailChunk000Sub001Block176Part021SupportExplicit : Finset ℕ :=
  ([15546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part021 : ℚ :=
  (16779393269 : ℚ) / 36006084264897600

def SurrogateDiagonalTailChunk000Sub001Block176Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15546
    = surrogateDiagTailX0RatChunk000Sub001Block176Part021

theorem surrogateDiagonalTailChunk000Sub001Block176Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part021] using hcert

def TailChunk000Sub001Block176Part022SupportExplicit : Finset ℕ :=
  ([15547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part022 : ℚ :=
  (12356031767 : ℚ) / 1574250188168217600

def SurrogateDiagonalTailChunk000Sub001Block176Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15547
    = surrogateDiagTailX0RatChunk000Sub001Block176Part022

theorem surrogateDiagonalTailChunk000Sub001Block176Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part022] using hcert

def TailChunk000Sub001Block176Part023SupportExplicit : Finset ℕ :=
  ([15549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part023 : ℚ :=
  (66943562923 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk000Sub001Block176Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15549
    = surrogateDiagTailX0RatChunk000Sub001Block176Part023

theorem surrogateDiagonalTailChunk000Sub001Block176Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part023] using hcert

def TailChunk000Sub001Block176Part024SupportExplicit : Finset ℕ :=
  ([15551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block176Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block176Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15551
    = surrogateDiagTailX0RatChunk000Sub001Block176Part024

theorem surrogateDiagonalTailChunk000Sub001Block176Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block176Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block176Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block176Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block176Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block176Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block176Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block176HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block176Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block176Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block176Part000
    + surrogateDiagTailX0RatChunk000Sub001Block176Part001
    + surrogateDiagTailX0RatChunk000Sub001Block176Part002
    + surrogateDiagTailX0RatChunk000Sub001Block176Part003
    + surrogateDiagTailX0RatChunk000Sub001Block176Part004
    + surrogateDiagTailX0RatChunk000Sub001Block176Part005
    + surrogateDiagTailX0RatChunk000Sub001Block176Part006
    + surrogateDiagTailX0RatChunk000Sub001Block176Part007
    + surrogateDiagTailX0RatChunk000Sub001Block176Part008
    + surrogateDiagTailX0RatChunk000Sub001Block176Part009

def surrogateDiagonalTailChunk000Sub001Block176MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block176Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block176Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block176Part010
    + surrogateDiagTailX0RatChunk000Sub001Block176Part011
    + surrogateDiagTailX0RatChunk000Sub001Block176Part012
    + surrogateDiagTailX0RatChunk000Sub001Block176Part013
    + surrogateDiagTailX0RatChunk000Sub001Block176Part014
    + surrogateDiagTailX0RatChunk000Sub001Block176Part015
    + surrogateDiagTailX0RatChunk000Sub001Block176Part016
    + surrogateDiagTailX0RatChunk000Sub001Block176Part017
    + surrogateDiagTailX0RatChunk000Sub001Block176Part018
    + surrogateDiagTailX0RatChunk000Sub001Block176Part019

def surrogateDiagonalTailChunk000Sub001Block176TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block176Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block176Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block176Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block176Part020
    + surrogateDiagTailX0RatChunk000Sub001Block176Part021
    + surrogateDiagTailX0RatChunk000Sub001Block176Part022
    + surrogateDiagTailX0RatChunk000Sub001Block176Part023
    + surrogateDiagTailX0RatChunk000Sub001Block176Part024

def surrogateDiagonalTailChunk000Sub001Block176Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block176HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block176MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block176TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block176 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block176Part000
    + surrogateDiagTailX0RatChunk000Sub001Block176Part001
    + surrogateDiagTailX0RatChunk000Sub001Block176Part002
    + surrogateDiagTailX0RatChunk000Sub001Block176Part003
    + surrogateDiagTailX0RatChunk000Sub001Block176Part004
    + surrogateDiagTailX0RatChunk000Sub001Block176Part005
    + surrogateDiagTailX0RatChunk000Sub001Block176Part006
    + surrogateDiagTailX0RatChunk000Sub001Block176Part007
    + surrogateDiagTailX0RatChunk000Sub001Block176Part008
    + surrogateDiagTailX0RatChunk000Sub001Block176Part009
    + surrogateDiagTailX0RatChunk000Sub001Block176Part010
    + surrogateDiagTailX0RatChunk000Sub001Block176Part011
    + surrogateDiagTailX0RatChunk000Sub001Block176Part012
    + surrogateDiagTailX0RatChunk000Sub001Block176Part013
    + surrogateDiagTailX0RatChunk000Sub001Block176Part014
    + surrogateDiagTailX0RatChunk000Sub001Block176Part015
    + surrogateDiagTailX0RatChunk000Sub001Block176Part016
    + surrogateDiagTailX0RatChunk000Sub001Block176Part017
    + surrogateDiagTailX0RatChunk000Sub001Block176Part018
    + surrogateDiagTailX0RatChunk000Sub001Block176Part019
    + surrogateDiagTailX0RatChunk000Sub001Block176Part020
    + surrogateDiagTailX0RatChunk000Sub001Block176Part021
    + surrogateDiagTailX0RatChunk000Sub001Block176Part022
    + surrogateDiagTailX0RatChunk000Sub001Block176Part023
    + surrogateDiagTailX0RatChunk000Sub001Block176Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block176_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block176Head + surrogateDiagTailX0RatChunk000Sub001Block176Mid + surrogateDiagTailX0RatChunk000Sub001Block176Tail =
      surrogateDiagTailX0RatChunk000Sub001Block176 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block176Head surrogateDiagTailX0RatChunk000Sub001Block176Mid surrogateDiagTailX0RatChunk000Sub001Block176Tail surrogateDiagTailX0RatChunk000Sub001Block176
  ring

def SurrogateDiagonalTailChunk000Sub001Block176HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block176HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block176Head

def SurrogateDiagonalTailChunk000Sub001Block176MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block176MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block176Mid

def SurrogateDiagonalTailChunk000Sub001Block176TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block176TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block176Tail

theorem surrogateDiagonalTailChunk000Sub001Block176_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block176HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block176MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block176TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block176Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block176 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block176HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block176MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block176TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block176Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block176_eq_head_add_mid_add_tail

/-- Block 177 covers tail-support indices [9425,9450) and q from 15553 to 15591. -/

def TailChunk000Sub001Block177Part000SupportExplicit : Finset ℕ :=
  ([15553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part000 : ℚ :=
  (28754821 : ℚ) / 50749155301500000

def SurrogateDiagonalTailChunk000Sub001Block177Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15553
    = surrogateDiagTailX0RatChunk000Sub001Block177Part000

theorem surrogateDiagonalTailChunk000Sub001Block177Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part000] using hcert

def TailChunk000Sub001Block177Part001SupportExplicit : Finset ℕ :=
  ([15554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part001 : ℚ :=
  (18018085927 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk000Sub001Block177Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15554
    = surrogateDiagTailX0RatChunk000Sub001Block177Part001

theorem surrogateDiagonalTailChunk000Sub001Block177Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part001] using hcert

def TailChunk000Sub001Block177Part002SupportExplicit : Finset ℕ :=
  ([15555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part002 : ℚ :=
  (21536644469 : ℚ) / 115987309815398400

def SurrogateDiagonalTailChunk000Sub001Block177Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15555
    = surrogateDiagTailX0RatChunk000Sub001Block177Part002

theorem surrogateDiagonalTailChunk000Sub001Block177Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part002] using hcert

def TailChunk000Sub001Block177Part003SupportExplicit : Finset ℕ :=
  ([15557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part003 : ℚ :=
  (116134747 : ℚ) / 132774276969884880

def SurrogateDiagonalTailChunk000Sub001Block177Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15557
    = surrogateDiagTailX0RatChunk000Sub001Block177Part003

theorem surrogateDiagonalTailChunk000Sub001Block177Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part003] using hcert

def TailChunk000Sub001Block177Part004SupportExplicit : Finset ℕ :=
  ([15558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part004 : ℚ :=
  (420132452075 : ℚ) / 902935721419997184

def SurrogateDiagonalTailChunk000Sub001Block177Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15558
    = surrogateDiagTailX0RatChunk000Sub001Block177Part004

theorem surrogateDiagonalTailChunk000Sub001Block177Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part004] using hcert

def TailChunk000Sub001Block177Part005SupportExplicit : Finset ℕ :=
  ([15559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block177Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15559
    = surrogateDiagTailX0RatChunk000Sub001Block177Part005

theorem surrogateDiagonalTailChunk000Sub001Block177Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part005] using hcert

def TailChunk000Sub001Block177Part006SupportExplicit : Finset ℕ :=
  ([15562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part006 : ℚ :=
  (333239707 : ℚ) / 31646953125000000

def SurrogateDiagonalTailChunk000Sub001Block177Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15562
    = surrogateDiagTailX0RatChunk000Sub001Block177Part006

theorem surrogateDiagonalTailChunk000Sub001Block177Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part006] using hcert

def TailChunk000Sub001Block177Part007SupportExplicit : Finset ℕ :=
  ([15563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part007 : ℚ :=
  (42002211275 : ℚ) / 68296674793671926784

def SurrogateDiagonalTailChunk000Sub001Block177Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15563
    = surrogateDiagTailX0RatChunk000Sub001Block177Part007

theorem surrogateDiagonalTailChunk000Sub001Block177Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part007] using hcert

def TailChunk000Sub001Block177Part008SupportExplicit : Finset ℕ :=
  ([15565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part008 : ℚ :=
  (2752051 : ℚ) / 85068811960320

def SurrogateDiagonalTailChunk000Sub001Block177Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15565
    = surrogateDiagTailX0RatChunk000Sub001Block177Part008

theorem surrogateDiagonalTailChunk000Sub001Block177Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part008] using hcert

def TailChunk000Sub001Block177Part009SupportExplicit : Finset ℕ :=
  ([15566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part009 : ℚ :=
  (139183721 : ℚ) / 16335936498792960

def SurrogateDiagonalTailChunk000Sub001Block177Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15566
    = surrogateDiagTailX0RatChunk000Sub001Block177Part009

theorem surrogateDiagonalTailChunk000Sub001Block177Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part009] using hcert

def TailChunk000Sub001Block177Part010SupportExplicit : Finset ℕ :=
  ([15567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part010 : ℚ :=
  (210354257225 : ℚ) / 3622903148934318336

def SurrogateDiagonalTailChunk000Sub001Block177Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15567
    = surrogateDiagTailX0RatChunk000Sub001Block177Part010

theorem surrogateDiagonalTailChunk000Sub001Block177Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part010] using hcert

def TailChunk000Sub001Block177Part011SupportExplicit : Finset ℕ :=
  ([15569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block177Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15569
    = surrogateDiagTailX0RatChunk000Sub001Block177Part011

theorem surrogateDiagonalTailChunk000Sub001Block177Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part011] using hcert

def TailChunk000Sub001Block177Part012SupportExplicit : Finset ℕ :=
  ([15571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part012 : ℚ :=
  (103275813725 : ℚ) / 61160970797354148864

def SurrogateDiagonalTailChunk000Sub001Block177Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15571
    = surrogateDiagTailX0RatChunk000Sub001Block177Part012

theorem surrogateDiagonalTailChunk000Sub001Block177Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part012] using hcert

def TailChunk000Sub001Block177Part013SupportExplicit : Finset ℕ :=
  ([15573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part013 : ℚ :=
  (279472132575 : ℚ) / 4114411505394434048

def SurrogateDiagonalTailChunk000Sub001Block177Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15573
    = surrogateDiagTailX0RatChunk000Sub001Block177Part013

theorem surrogateDiagonalTailChunk000Sub001Block177Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part013] using hcert

def TailChunk000Sub001Block177Part014SupportExplicit : Finset ℕ :=
  ([15574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part014 : ℚ :=
  (15737103325 : ℚ) / 510050557644466176

def SurrogateDiagonalTailChunk000Sub001Block177Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15574
    = surrogateDiagTailX0RatChunk000Sub001Block177Part014

theorem surrogateDiagonalTailChunk000Sub001Block177Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part014] using hcert

def TailChunk000Sub001Block177Part015SupportExplicit : Finset ℕ :=
  ([15577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part015 : ℚ :=
  (12993089 : ℚ) / 11853740770099200

def SurrogateDiagonalTailChunk000Sub001Block177Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15577
    = surrogateDiagTailX0RatChunk000Sub001Block177Part015

theorem surrogateDiagonalTailChunk000Sub001Block177Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part015] using hcert

def TailChunk000Sub001Block177Part016SupportExplicit : Finset ℕ :=
  ([15578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block177Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15578
    = surrogateDiagTailX0RatChunk000Sub001Block177Part016

theorem surrogateDiagonalTailChunk000Sub001Block177Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part016] using hcert

def TailChunk000Sub001Block177Part017SupportExplicit : Finset ℕ :=
  ([15581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block177Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15581
    = surrogateDiagTailX0RatChunk000Sub001Block177Part017

theorem surrogateDiagonalTailChunk000Sub001Block177Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part017] using hcert

def TailChunk000Sub001Block177Part018SupportExplicit : Finset ℕ :=
  ([15583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block177Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15583
    = surrogateDiagTailX0RatChunk000Sub001Block177Part018

theorem surrogateDiagonalTailChunk000Sub001Block177Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part018] using hcert

def TailChunk000Sub001Block177Part019SupportExplicit : Finset ℕ :=
  ([15585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part019 : ℚ :=
  (219151430225 : ℚ) / 1486230720320802816

def SurrogateDiagonalTailChunk000Sub001Block177Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15585
    = surrogateDiagTailX0RatChunk000Sub001Block177Part019

theorem surrogateDiagonalTailChunk000Sub001Block177Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part019] using hcert

def TailChunk000Sub001Block177Part020SupportExplicit : Finset ℕ :=
  ([15586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block177Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15586
    = surrogateDiagTailX0RatChunk000Sub001Block177Part020

theorem surrogateDiagonalTailChunk000Sub001Block177Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part020] using hcert

def TailChunk000Sub001Block177Part021SupportExplicit : Finset ℕ :=
  ([15587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part021 : ℚ :=
  (31058578981 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk000Sub001Block177Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15587
    = surrogateDiagTailX0RatChunk000Sub001Block177Part021

theorem surrogateDiagonalTailChunk000Sub001Block177Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part021] using hcert

def TailChunk000Sub001Block177Part022SupportExplicit : Finset ℕ :=
  ([15589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part022 : ℚ :=
  (15871280423 : ℚ) / 1213151936879001600

def SurrogateDiagonalTailChunk000Sub001Block177Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15589
    = surrogateDiagTailX0RatChunk000Sub001Block177Part022

theorem surrogateDiagonalTailChunk000Sub001Block177Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part022] using hcert

def TailChunk000Sub001Block177Part023SupportExplicit : Finset ℕ :=
  ([15590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part023 : ℚ :=
  (57024867725 : ℚ) / 471461952615495936

def SurrogateDiagonalTailChunk000Sub001Block177Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15590
    = surrogateDiagTailX0RatChunk000Sub001Block177Part023

theorem surrogateDiagonalTailChunk000Sub001Block177Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part023] using hcert

def TailChunk000Sub001Block177Part024SupportExplicit : Finset ℕ :=
  ([15591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block177Part024 : ℚ :=
  (13187703575 : ℚ) / 227831327938236816

def SurrogateDiagonalTailChunk000Sub001Block177Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15591
    = surrogateDiagTailX0RatChunk000Sub001Block177Part024

theorem surrogateDiagonalTailChunk000Sub001Block177Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block177Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block177Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block177Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block177Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block177Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block177Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block177HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block177Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block177Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block177Part000
    + surrogateDiagTailX0RatChunk000Sub001Block177Part001
    + surrogateDiagTailX0RatChunk000Sub001Block177Part002
    + surrogateDiagTailX0RatChunk000Sub001Block177Part003
    + surrogateDiagTailX0RatChunk000Sub001Block177Part004
    + surrogateDiagTailX0RatChunk000Sub001Block177Part005
    + surrogateDiagTailX0RatChunk000Sub001Block177Part006
    + surrogateDiagTailX0RatChunk000Sub001Block177Part007
    + surrogateDiagTailX0RatChunk000Sub001Block177Part008
    + surrogateDiagTailX0RatChunk000Sub001Block177Part009

def surrogateDiagonalTailChunk000Sub001Block177MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block177Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block177Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block177Part010
    + surrogateDiagTailX0RatChunk000Sub001Block177Part011
    + surrogateDiagTailX0RatChunk000Sub001Block177Part012
    + surrogateDiagTailX0RatChunk000Sub001Block177Part013
    + surrogateDiagTailX0RatChunk000Sub001Block177Part014
    + surrogateDiagTailX0RatChunk000Sub001Block177Part015
    + surrogateDiagTailX0RatChunk000Sub001Block177Part016
    + surrogateDiagTailX0RatChunk000Sub001Block177Part017
    + surrogateDiagTailX0RatChunk000Sub001Block177Part018
    + surrogateDiagTailX0RatChunk000Sub001Block177Part019

def surrogateDiagonalTailChunk000Sub001Block177TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block177Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block177Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block177Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block177Part020
    + surrogateDiagTailX0RatChunk000Sub001Block177Part021
    + surrogateDiagTailX0RatChunk000Sub001Block177Part022
    + surrogateDiagTailX0RatChunk000Sub001Block177Part023
    + surrogateDiagTailX0RatChunk000Sub001Block177Part024

def surrogateDiagonalTailChunk000Sub001Block177Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block177HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block177MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block177TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block177 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block177Part000
    + surrogateDiagTailX0RatChunk000Sub001Block177Part001
    + surrogateDiagTailX0RatChunk000Sub001Block177Part002
    + surrogateDiagTailX0RatChunk000Sub001Block177Part003
    + surrogateDiagTailX0RatChunk000Sub001Block177Part004
    + surrogateDiagTailX0RatChunk000Sub001Block177Part005
    + surrogateDiagTailX0RatChunk000Sub001Block177Part006
    + surrogateDiagTailX0RatChunk000Sub001Block177Part007
    + surrogateDiagTailX0RatChunk000Sub001Block177Part008
    + surrogateDiagTailX0RatChunk000Sub001Block177Part009
    + surrogateDiagTailX0RatChunk000Sub001Block177Part010
    + surrogateDiagTailX0RatChunk000Sub001Block177Part011
    + surrogateDiagTailX0RatChunk000Sub001Block177Part012
    + surrogateDiagTailX0RatChunk000Sub001Block177Part013
    + surrogateDiagTailX0RatChunk000Sub001Block177Part014
    + surrogateDiagTailX0RatChunk000Sub001Block177Part015
    + surrogateDiagTailX0RatChunk000Sub001Block177Part016
    + surrogateDiagTailX0RatChunk000Sub001Block177Part017
    + surrogateDiagTailX0RatChunk000Sub001Block177Part018
    + surrogateDiagTailX0RatChunk000Sub001Block177Part019
    + surrogateDiagTailX0RatChunk000Sub001Block177Part020
    + surrogateDiagTailX0RatChunk000Sub001Block177Part021
    + surrogateDiagTailX0RatChunk000Sub001Block177Part022
    + surrogateDiagTailX0RatChunk000Sub001Block177Part023
    + surrogateDiagTailX0RatChunk000Sub001Block177Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block177_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block177Head + surrogateDiagTailX0RatChunk000Sub001Block177Mid + surrogateDiagTailX0RatChunk000Sub001Block177Tail =
      surrogateDiagTailX0RatChunk000Sub001Block177 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block177Head surrogateDiagTailX0RatChunk000Sub001Block177Mid surrogateDiagTailX0RatChunk000Sub001Block177Tail surrogateDiagTailX0RatChunk000Sub001Block177
  ring

def SurrogateDiagonalTailChunk000Sub001Block177HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block177HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block177Head

def SurrogateDiagonalTailChunk000Sub001Block177MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block177MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block177Mid

def SurrogateDiagonalTailChunk000Sub001Block177TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block177TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block177Tail

theorem surrogateDiagonalTailChunk000Sub001Block177_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block177HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block177MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block177TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block177Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block177 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block177HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block177MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block177TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block177Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block177_eq_head_add_mid_add_tail

/-- Block 178 covers tail-support indices [9450,9475) and q from 15593 to 15634. -/

def TailChunk000Sub001Block178Part000SupportExplicit : Finset ℕ :=
  ([15593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part000 : ℚ :=
  (6035424739 : ℚ) / 5145016094755459200

def SurrogateDiagonalTailChunk000Sub001Block178Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15593
    = surrogateDiagTailX0RatChunk000Sub001Block178Part000

theorem surrogateDiagonalTailChunk000Sub001Block178Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part000] using hcert

def TailChunk000Sub001Block178Part001SupportExplicit : Finset ℕ :=
  ([15594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part001 : ℚ :=
  (140227976925 : ℚ) / 245786714977599488

def SurrogateDiagonalTailChunk000Sub001Block178Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15594
    = surrogateDiagTailX0RatChunk000Sub001Block178Part001

theorem surrogateDiagonalTailChunk000Sub001Block178Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part001] using hcert

def TailChunk000Sub001Block178Part002SupportExplicit : Finset ℕ :=
  ([15595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part002 : ℚ :=
  (202957015875 : ℚ) / 20167404676912715776

def SurrogateDiagonalTailChunk000Sub001Block178Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15595
    = surrogateDiagTailX0RatChunk000Sub001Block178Part002

theorem surrogateDiagonalTailChunk000Sub001Block178Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part002] using hcert

def TailChunk000Sub001Block178Part003SupportExplicit : Finset ℕ :=
  ([15598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part003 : ℚ :=
  (8886661399 : ℚ) / 251315850815539200

def SurrogateDiagonalTailChunk000Sub001Block178Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15598
    = surrogateDiagTailX0RatChunk000Sub001Block178Part003

theorem surrogateDiagonalTailChunk000Sub001Block178Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part003] using hcert

def TailChunk000Sub001Block178Part004SupportExplicit : Finset ℕ :=
  ([15599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part004 : ℚ :=
  (1030080913 : ℚ) / 474714262645355520

def SurrogateDiagonalTailChunk000Sub001Block178Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15599
    = surrogateDiagTailX0RatChunk000Sub001Block178Part004

theorem surrogateDiagonalTailChunk000Sub001Block178Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part004] using hcert

def TailChunk000Sub001Block178Part005SupportExplicit : Finset ℕ :=
  ([15601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block178Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15601
    = surrogateDiagTailX0RatChunk000Sub001Block178Part005

theorem surrogateDiagonalTailChunk000Sub001Block178Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part005] using hcert

def TailChunk000Sub001Block178Part006SupportExplicit : Finset ℕ :=
  ([15602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part006 : ℚ :=
  (93713558875 : ℚ) / 7928630163751600128

def SurrogateDiagonalTailChunk000Sub001Block178Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15602
    = surrogateDiagTailX0RatChunk000Sub001Block178Part006

theorem surrogateDiagonalTailChunk000Sub001Block178Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part006] using hcert

def TailChunk000Sub001Block178Part007SupportExplicit : Finset ℕ :=
  ([15603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part007 : ℚ :=
  (61315575575 : ℚ) / 582108177100068864

def SurrogateDiagonalTailChunk000Sub001Block178Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15603
    = surrogateDiagTailX0RatChunk000Sub001Block178Part007

theorem surrogateDiagonalTailChunk000Sub001Block178Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part007] using hcert

def TailChunk000Sub001Block178Part008SupportExplicit : Finset ℕ :=
  ([15605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part008 : ℚ :=
  (4877206379 : ℚ) / 485260774751600640

def SurrogateDiagonalTailChunk000Sub001Block178Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15605
    = surrogateDiagTailX0RatChunk000Sub001Block178Part008

theorem surrogateDiagonalTailChunk000Sub001Block178Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part008] using hcert

def TailChunk000Sub001Block178Part009SupportExplicit : Finset ℕ :=
  ([15607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block178Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15607
    = surrogateDiagTailX0RatChunk000Sub001Block178Part009

theorem surrogateDiagonalTailChunk000Sub001Block178Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part009] using hcert

def TailChunk000Sub001Block178Part010SupportExplicit : Finset ℕ :=
  ([15610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part010 : ℚ :=
  (583392105025 : ℚ) / 2015040240855318528

def SurrogateDiagonalTailChunk000Sub001Block178Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15610
    = surrogateDiagTailX0RatChunk000Sub001Block178Part010

theorem surrogateDiagonalTailChunk000Sub001Block178Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part010] using hcert

def TailChunk000Sub001Block178Part011SupportExplicit : Finset ℕ :=
  ([15611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part011 : ℚ :=
  (11802583175 : ℚ) / 17181637563989200896

def SurrogateDiagonalTailChunk000Sub001Block178Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15611
    = surrogateDiagTailX0RatChunk000Sub001Block178Part011

theorem surrogateDiagonalTailChunk000Sub001Block178Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part011] using hcert

def TailChunk000Sub001Block178Part012SupportExplicit : Finset ℕ :=
  ([15613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part012 : ℚ :=
  (7270740797 : ℚ) / 2150338461696000000

def SurrogateDiagonalTailChunk000Sub001Block178Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15613
    = surrogateDiagTailX0RatChunk000Sub001Block178Part012

theorem surrogateDiagonalTailChunk000Sub001Block178Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part012] using hcert

def TailChunk000Sub001Block178Part013SupportExplicit : Finset ℕ :=
  ([15614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part013 : ℚ :=
  (114197497 : ℚ) / 12100693702809600

def SurrogateDiagonalTailChunk000Sub001Block178Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15614
    = surrogateDiagTailX0RatChunk000Sub001Block178Part013

theorem surrogateDiagonalTailChunk000Sub001Block178Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part013] using hcert

def TailChunk000Sub001Block178Part014SupportExplicit : Finset ℕ :=
  ([15617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part014 : ℚ :=
  (768523564075 : ℚ) / 64477399895431446528

def SurrogateDiagonalTailChunk000Sub001Block178Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15617
    = surrogateDiagTailX0RatChunk000Sub001Block178Part014

theorem surrogateDiagonalTailChunk000Sub001Block178Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part014] using hcert

def TailChunk000Sub001Block178Part015SupportExplicit : Finset ℕ :=
  ([15618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part015 : ℚ :=
  (35092828325 : ℚ) / 59866139553103872

def SurrogateDiagonalTailChunk000Sub001Block178Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15618
    = surrogateDiagTailX0RatChunk000Sub001Block178Part015

theorem surrogateDiagonalTailChunk000Sub001Block178Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part015] using hcert

def TailChunk000Sub001Block178Part016SupportExplicit : Finset ℕ :=
  ([15619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block178Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15619
    = surrogateDiagTailX0RatChunk000Sub001Block178Part016

theorem surrogateDiagonalTailChunk000Sub001Block178Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part016] using hcert

def TailChunk000Sub001Block178Part017SupportExplicit : Finset ℕ :=
  ([15621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part017 : ℚ :=
  (4088839243 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk000Sub001Block178Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15621
    = surrogateDiagTailX0RatChunk000Sub001Block178Part017

theorem surrogateDiagonalTailChunk000Sub001Block178Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part017] using hcert

def TailChunk000Sub001Block178Part018SupportExplicit : Finset ℕ :=
  ([15622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part018 : ℚ :=
  (18347564275 : ℚ) / 2827867462596919296

def SurrogateDiagonalTailChunk000Sub001Block178Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15622
    = surrogateDiagTailX0RatChunk000Sub001Block178Part018

theorem surrogateDiagonalTailChunk000Sub001Block178Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part018] using hcert

def TailChunk000Sub001Block178Part019SupportExplicit : Finset ℕ :=
  ([15623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part019 : ℚ :=
  (268139214025 : ℚ) / 116379775291233927168

def SurrogateDiagonalTailChunk000Sub001Block178Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15623
    = surrogateDiagTailX0RatChunk000Sub001Block178Part019

theorem surrogateDiagonalTailChunk000Sub001Block178Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part019] using hcert

def TailChunk000Sub001Block178Part020SupportExplicit : Finset ℕ :=
  ([15626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part020 : ℚ :=
  (29725319 : ℚ) / 58331664000000

def SurrogateDiagonalTailChunk000Sub001Block178Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15626
    = surrogateDiagTailX0RatChunk000Sub001Block178Part020

theorem surrogateDiagonalTailChunk000Sub001Block178Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part020] using hcert

def TailChunk000Sub001Block178Part021SupportExplicit : Finset ℕ :=
  ([15627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part021 : ℚ :=
  (6781440479125 : ℚ) / 29432743372147949568

def SurrogateDiagonalTailChunk000Sub001Block178Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15627
    = surrogateDiagTailX0RatChunk000Sub001Block178Part021

theorem surrogateDiagonalTailChunk000Sub001Block178Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part021] using hcert

def TailChunk000Sub001Block178Part022SupportExplicit : Finset ℕ :=
  ([15629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part022 : ℚ :=
  (3816650640625 : ℚ) / 37288977759203142432

def SurrogateDiagonalTailChunk000Sub001Block178Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15629
    = surrogateDiagTailX0RatChunk000Sub001Block178Part022

theorem surrogateDiagonalTailChunk000Sub001Block178Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part022] using hcert

def TailChunk000Sub001Block178Part023SupportExplicit : Finset ℕ :=
  ([15630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part023 : ℚ :=
  (8210457461 : ℚ) / 3744296101478400

def SurrogateDiagonalTailChunk000Sub001Block178Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15630
    = surrogateDiagTailX0RatChunk000Sub001Block178Part023

theorem surrogateDiagonalTailChunk000Sub001Block178Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part023] using hcert

def TailChunk000Sub001Block178Part024SupportExplicit : Finset ℕ :=
  ([15634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block178Part024 : ℚ :=
  (954773265625 : ℚ) / 2332948062626222592

def SurrogateDiagonalTailChunk000Sub001Block178Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15634
    = surrogateDiagTailX0RatChunk000Sub001Block178Part024

theorem surrogateDiagonalTailChunk000Sub001Block178Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block178Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block178Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block178Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block178Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block178Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block178Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block178HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block178Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block178Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block178Part000
    + surrogateDiagTailX0RatChunk000Sub001Block178Part001
    + surrogateDiagTailX0RatChunk000Sub001Block178Part002
    + surrogateDiagTailX0RatChunk000Sub001Block178Part003
    + surrogateDiagTailX0RatChunk000Sub001Block178Part004
    + surrogateDiagTailX0RatChunk000Sub001Block178Part005
    + surrogateDiagTailX0RatChunk000Sub001Block178Part006
    + surrogateDiagTailX0RatChunk000Sub001Block178Part007
    + surrogateDiagTailX0RatChunk000Sub001Block178Part008
    + surrogateDiagTailX0RatChunk000Sub001Block178Part009

def surrogateDiagonalTailChunk000Sub001Block178MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block178Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block178Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block178Part010
    + surrogateDiagTailX0RatChunk000Sub001Block178Part011
    + surrogateDiagTailX0RatChunk000Sub001Block178Part012
    + surrogateDiagTailX0RatChunk000Sub001Block178Part013
    + surrogateDiagTailX0RatChunk000Sub001Block178Part014
    + surrogateDiagTailX0RatChunk000Sub001Block178Part015
    + surrogateDiagTailX0RatChunk000Sub001Block178Part016
    + surrogateDiagTailX0RatChunk000Sub001Block178Part017
    + surrogateDiagTailX0RatChunk000Sub001Block178Part018
    + surrogateDiagTailX0RatChunk000Sub001Block178Part019

def surrogateDiagonalTailChunk000Sub001Block178TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block178Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block178Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block178Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block178Part020
    + surrogateDiagTailX0RatChunk000Sub001Block178Part021
    + surrogateDiagTailX0RatChunk000Sub001Block178Part022
    + surrogateDiagTailX0RatChunk000Sub001Block178Part023
    + surrogateDiagTailX0RatChunk000Sub001Block178Part024

def surrogateDiagonalTailChunk000Sub001Block178Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block178HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block178MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block178TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block178 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block178Part000
    + surrogateDiagTailX0RatChunk000Sub001Block178Part001
    + surrogateDiagTailX0RatChunk000Sub001Block178Part002
    + surrogateDiagTailX0RatChunk000Sub001Block178Part003
    + surrogateDiagTailX0RatChunk000Sub001Block178Part004
    + surrogateDiagTailX0RatChunk000Sub001Block178Part005
    + surrogateDiagTailX0RatChunk000Sub001Block178Part006
    + surrogateDiagTailX0RatChunk000Sub001Block178Part007
    + surrogateDiagTailX0RatChunk000Sub001Block178Part008
    + surrogateDiagTailX0RatChunk000Sub001Block178Part009
    + surrogateDiagTailX0RatChunk000Sub001Block178Part010
    + surrogateDiagTailX0RatChunk000Sub001Block178Part011
    + surrogateDiagTailX0RatChunk000Sub001Block178Part012
    + surrogateDiagTailX0RatChunk000Sub001Block178Part013
    + surrogateDiagTailX0RatChunk000Sub001Block178Part014
    + surrogateDiagTailX0RatChunk000Sub001Block178Part015
    + surrogateDiagTailX0RatChunk000Sub001Block178Part016
    + surrogateDiagTailX0RatChunk000Sub001Block178Part017
    + surrogateDiagTailX0RatChunk000Sub001Block178Part018
    + surrogateDiagTailX0RatChunk000Sub001Block178Part019
    + surrogateDiagTailX0RatChunk000Sub001Block178Part020
    + surrogateDiagTailX0RatChunk000Sub001Block178Part021
    + surrogateDiagTailX0RatChunk000Sub001Block178Part022
    + surrogateDiagTailX0RatChunk000Sub001Block178Part023
    + surrogateDiagTailX0RatChunk000Sub001Block178Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block178_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block178Head + surrogateDiagTailX0RatChunk000Sub001Block178Mid + surrogateDiagTailX0RatChunk000Sub001Block178Tail =
      surrogateDiagTailX0RatChunk000Sub001Block178 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block178Head surrogateDiagTailX0RatChunk000Sub001Block178Mid surrogateDiagTailX0RatChunk000Sub001Block178Tail surrogateDiagTailX0RatChunk000Sub001Block178
  ring

def SurrogateDiagonalTailChunk000Sub001Block178HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block178HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block178Head

def SurrogateDiagonalTailChunk000Sub001Block178MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block178MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block178Mid

def SurrogateDiagonalTailChunk000Sub001Block178TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block178TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block178Tail

theorem surrogateDiagonalTailChunk000Sub001Block178_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block178HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block178MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block178TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block178Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block178 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block178HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block178MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block178TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block178Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block178_eq_head_add_mid_add_tail

/-- Block 179 covers tail-support indices [9475,9500) and q from 15635 to 15673. -/

def TailChunk000Sub001Block179Part000SupportExplicit : Finset ℕ :=
  ([15635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part000 : ℚ :=
  (4898047441025 : ℚ) / 26482694909497442304

def SurrogateDiagonalTailChunk000Sub001Block179Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15635
    = surrogateDiagTailX0RatChunk000Sub001Block179Part000

theorem surrogateDiagonalTailChunk000Sub001Block179Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part000] using hcert

def TailChunk000Sub001Block179Part001SupportExplicit : Finset ℕ :=
  ([15637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part001 : ℚ :=
  (217198461025 : ℚ) / 1872510128392260402

def SurrogateDiagonalTailChunk000Sub001Block179Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15637
    = surrogateDiagTailX0RatChunk000Sub001Block179Part001

theorem surrogateDiagonalTailChunk000Sub001Block179Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part001] using hcert

def TailChunk000Sub001Block179Part002SupportExplicit : Finset ℕ :=
  ([15638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part002 : ℚ :=
  (3116072487775 : ℚ) / 5026765651412502528

def SurrogateDiagonalTailChunk000Sub001Block179Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15638
    = surrogateDiagTailX0RatChunk000Sub001Block179Part002

theorem surrogateDiagonalTailChunk000Sub001Block179Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part002] using hcert

def TailChunk000Sub001Block179Part003SupportExplicit : Finset ℕ :=
  ([15639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part003 : ℚ :=
  (119543748443 : ℚ) / 424758214656000000

def SurrogateDiagonalTailChunk000Sub001Block179Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15639
    = surrogateDiagTailX0RatChunk000Sub001Block179Part003

theorem surrogateDiagonalTailChunk000Sub001Block179Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part003] using hcert

def TailChunk000Sub001Block179Part004SupportExplicit : Finset ℕ :=
  ([15641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part004 : ℚ :=
  (6116022025 : ℚ) / 59845823183442432

def SurrogateDiagonalTailChunk000Sub001Block179Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15641
    = surrogateDiagTailX0RatChunk000Sub001Block179Part004

theorem surrogateDiagonalTailChunk000Sub001Block179Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part004] using hcert

def TailChunk000Sub001Block179Part005SupportExplicit : Finset ℕ :=
  ([15643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part005 : ℚ :=
  (3823491390625 : ℚ) / 37422775456256365362

def SurrogateDiagonalTailChunk000Sub001Block179Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15643
    = surrogateDiagTailX0RatChunk000Sub001Block179Part005

theorem surrogateDiagonalTailChunk000Sub001Block179Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part005] using hcert

def TailChunk000Sub001Block179Part006SupportExplicit : Finset ℕ :=
  ([15645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part006 : ℚ :=
  (1877336458775 : ℚ) / 3184261121351614464

def SurrogateDiagonalTailChunk000Sub001Block179Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15645
    = surrogateDiagTailX0RatChunk000Sub001Block179Part006

theorem surrogateDiagonalTailChunk000Sub001Block179Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part006] using hcert

def TailChunk000Sub001Block179Part007SupportExplicit : Finset ℕ :=
  ([15646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part007 : ℚ :=
  (956239515625 : ℚ) / 2340119922780886482

def SurrogateDiagonalTailChunk000Sub001Block179Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15646
    = surrogateDiagTailX0RatChunk000Sub001Block179Part007

theorem surrogateDiagonalTailChunk000Sub001Block179Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part007] using hcert

def TailChunk000Sub001Block179Part008SupportExplicit : Finset ℕ :=
  ([15647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part008 : ℚ :=
  (3825447015625 : ℚ) / 37461069416242510482

def SurrogateDiagonalTailChunk000Sub001Block179Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15647
    = surrogateDiagTailX0RatChunk000Sub001Block179Part008

theorem surrogateDiagonalTailChunk000Sub001Block179Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part008] using hcert

def TailChunk000Sub001Block179Part009SupportExplicit : Finset ℕ :=
  ([15649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part009 : ℚ :=
  (3826425015625 : ℚ) / 37480227413379121152

def SurrogateDiagonalTailChunk000Sub001Block179Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15649
    = surrogateDiagTailX0RatChunk000Sub001Block179Part009

theorem surrogateDiagonalTailChunk000Sub001Block179Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part009] using hcert

def TailChunk000Sub001Block179Part010SupportExplicit : Finset ℕ :=
  ([15653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part010 : ℚ :=
  (32237167441 : ℚ) / 255602591737288200

def SurrogateDiagonalTailChunk000Sub001Block179Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15653
    = surrogateDiagTailX0RatChunk000Sub001Block179Part010

theorem surrogateDiagonalTailChunk000Sub001Block179Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part010] using hcert

def TailChunk000Sub001Block179Part011SupportExplicit : Finset ℕ :=
  ([15654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part011 : ℚ :=
  (1063242477725 : ℚ) / 925437713910595584

def SurrogateDiagonalTailChunk000Sub001Block179Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15654
    = surrogateDiagTailX0RatChunk000Sub001Block179Part011

theorem surrogateDiagonalTailChunk000Sub001Block179Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part011] using hcert

def TailChunk000Sub001Block179Part012SupportExplicit : Finset ℕ :=
  ([15655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part012 : ℚ :=
  (64765901729 : ℚ) / 345669120000000000

def SurrogateDiagonalTailChunk000Sub001Block179Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15655
    = surrogateDiagTailX0RatChunk000Sub001Block179Part012

theorem surrogateDiagonalTailChunk000Sub001Block179Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part012] using hcert

def TailChunk000Sub001Block179Part013SupportExplicit : Finset ℕ :=
  ([15657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part013 : ℚ :=
  (386139453325 : ℚ) / 1436787349274492928

def SurrogateDiagonalTailChunk000Sub001Block179Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15657
    = surrogateDiagTailX0RatChunk000Sub001Block179Part013

theorem surrogateDiagonalTailChunk000Sub001Block179Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part013] using hcert

def TailChunk000Sub001Block179Part014SupportExplicit : Finset ℕ :=
  ([15658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part014 : ℚ :=
  (957706890625 : ℚ) / 2347308305835769632

def SurrogateDiagonalTailChunk000Sub001Block179Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15658
    = surrogateDiagTailX0RatChunk000Sub001Block179Part014

theorem surrogateDiagonalTailChunk000Sub001Block179Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part014] using hcert

def TailChunk000Sub001Block179Part015SupportExplicit : Finset ℕ :=
  ([15659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part015 : ℚ :=
  (11564417217025 : ℚ) / 81006348729567725568

def SurrogateDiagonalTailChunk000Sub001Block179Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15659
    = surrogateDiagTailX0RatChunk000Sub001Block179Part015

theorem surrogateDiagonalTailChunk000Sub001Block179Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part015] using hcert

def TailChunk000Sub001Block179Part016SupportExplicit : Finset ℕ :=
  ([15661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part016 : ℚ :=
  (6131673025 : ℚ) / 60152527607261472

def SurrogateDiagonalTailChunk000Sub001Block179Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15661
    = surrogateDiagTailX0RatChunk000Sub001Block179Part016

theorem surrogateDiagonalTailChunk000Sub001Block179Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part016] using hcert

def TailChunk000Sub001Block179Part017SupportExplicit : Finset ℕ :=
  ([15662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part017 : ℚ :=
  (147177714229 : ℚ) / 333688484352000000

def SurrogateDiagonalTailChunk000Sub001Block179Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15662
    = surrogateDiagTailX0RatChunk000Sub001Block179Part017

theorem surrogateDiagonalTailChunk000Sub001Block179Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part017] using hcert

def TailChunk000Sub001Block179Part018SupportExplicit : Finset ℕ :=
  ([15663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part018 : ℚ :=
  (191457614925 : ℚ) / 740896224250873856

def SurrogateDiagonalTailChunk000Sub001Block179Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15663
    = surrogateDiagTailX0RatChunk000Sub001Block179Part018

theorem surrogateDiagonalTailChunk000Sub001Block179Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part018] using hcert

def TailChunk000Sub001Block179Part019SupportExplicit : Finset ℕ :=
  ([15665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part019 : ℚ :=
  (60753260099 : ℚ) / 293592877970227200

def SurrogateDiagonalTailChunk000Sub001Block179Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15665
    = surrogateDiagTailX0RatChunk000Sub001Block179Part019

theorem surrogateDiagonalTailChunk000Sub001Block179Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part019] using hcert

def TailChunk000Sub001Block179Part020SupportExplicit : Finset ℕ :=
  ([15666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part020 : ℚ :=
  (1759791606325 : ℚ) / 992941363241975808

def SurrogateDiagonalTailChunk000Sub001Block179Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15666
    = surrogateDiagTailX0RatChunk000Sub001Block179Part020

theorem surrogateDiagonalTailChunk000Sub001Block179Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part020] using hcert

def TailChunk000Sub001Block179Part021SupportExplicit : Finset ℕ :=
  ([15667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part021 : ℚ :=
  (3835232640625 : ℚ) / 37652980240033170642

def SurrogateDiagonalTailChunk000Sub001Block179Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15667
    = surrogateDiagTailX0RatChunk000Sub001Block179Part021

theorem surrogateDiagonalTailChunk000Sub001Block179Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part021] using hcert

def TailChunk000Sub001Block179Part022SupportExplicit : Finset ℕ :=
  ([15670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part022 : ℚ :=
  (2760579943825 : ℚ) / 3849761766864734208

def SurrogateDiagonalTailChunk000Sub001Block179Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15670
    = surrogateDiagTailX0RatChunk000Sub001Block179Part022

theorem surrogateDiagonalTailChunk000Sub001Block179Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part022] using hcert

def TailChunk000Sub001Block179Part023SupportExplicit : Finset ℕ :=
  ([15671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part023 : ℚ :=
  (6139506025 : ℚ) / 60306321143668242

def SurrogateDiagonalTailChunk000Sub001Block179Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15671
    = surrogateDiagTailX0RatChunk000Sub001Block179Part023

theorem surrogateDiagonalTailChunk000Sub001Block179Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part023] using hcert

def TailChunk000Sub001Block179Part024SupportExplicit : Finset ℕ :=
  ([15673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block179Part024 : ℚ :=
  (11585110807225 : ℚ) / 81296563750242380928

def SurrogateDiagonalTailChunk000Sub001Block179Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15673
    = surrogateDiagTailX0RatChunk000Sub001Block179Part024

theorem surrogateDiagonalTailChunk000Sub001Block179Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block179Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block179Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block179Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block179Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block179Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block179Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block179HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block179Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block179Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block179Part000
    + surrogateDiagTailX0RatChunk000Sub001Block179Part001
    + surrogateDiagTailX0RatChunk000Sub001Block179Part002
    + surrogateDiagTailX0RatChunk000Sub001Block179Part003
    + surrogateDiagTailX0RatChunk000Sub001Block179Part004
    + surrogateDiagTailX0RatChunk000Sub001Block179Part005
    + surrogateDiagTailX0RatChunk000Sub001Block179Part006
    + surrogateDiagTailX0RatChunk000Sub001Block179Part007
    + surrogateDiagTailX0RatChunk000Sub001Block179Part008
    + surrogateDiagTailX0RatChunk000Sub001Block179Part009

def surrogateDiagonalTailChunk000Sub001Block179MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block179Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block179Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block179Part010
    + surrogateDiagTailX0RatChunk000Sub001Block179Part011
    + surrogateDiagTailX0RatChunk000Sub001Block179Part012
    + surrogateDiagTailX0RatChunk000Sub001Block179Part013
    + surrogateDiagTailX0RatChunk000Sub001Block179Part014
    + surrogateDiagTailX0RatChunk000Sub001Block179Part015
    + surrogateDiagTailX0RatChunk000Sub001Block179Part016
    + surrogateDiagTailX0RatChunk000Sub001Block179Part017
    + surrogateDiagTailX0RatChunk000Sub001Block179Part018
    + surrogateDiagTailX0RatChunk000Sub001Block179Part019

def surrogateDiagonalTailChunk000Sub001Block179TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block179Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block179Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block179Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block179Part020
    + surrogateDiagTailX0RatChunk000Sub001Block179Part021
    + surrogateDiagTailX0RatChunk000Sub001Block179Part022
    + surrogateDiagTailX0RatChunk000Sub001Block179Part023
    + surrogateDiagTailX0RatChunk000Sub001Block179Part024

def surrogateDiagonalTailChunk000Sub001Block179Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block179HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block179MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block179TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block179 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block179Part000
    + surrogateDiagTailX0RatChunk000Sub001Block179Part001
    + surrogateDiagTailX0RatChunk000Sub001Block179Part002
    + surrogateDiagTailX0RatChunk000Sub001Block179Part003
    + surrogateDiagTailX0RatChunk000Sub001Block179Part004
    + surrogateDiagTailX0RatChunk000Sub001Block179Part005
    + surrogateDiagTailX0RatChunk000Sub001Block179Part006
    + surrogateDiagTailX0RatChunk000Sub001Block179Part007
    + surrogateDiagTailX0RatChunk000Sub001Block179Part008
    + surrogateDiagTailX0RatChunk000Sub001Block179Part009
    + surrogateDiagTailX0RatChunk000Sub001Block179Part010
    + surrogateDiagTailX0RatChunk000Sub001Block179Part011
    + surrogateDiagTailX0RatChunk000Sub001Block179Part012
    + surrogateDiagTailX0RatChunk000Sub001Block179Part013
    + surrogateDiagTailX0RatChunk000Sub001Block179Part014
    + surrogateDiagTailX0RatChunk000Sub001Block179Part015
    + surrogateDiagTailX0RatChunk000Sub001Block179Part016
    + surrogateDiagTailX0RatChunk000Sub001Block179Part017
    + surrogateDiagTailX0RatChunk000Sub001Block179Part018
    + surrogateDiagTailX0RatChunk000Sub001Block179Part019
    + surrogateDiagTailX0RatChunk000Sub001Block179Part020
    + surrogateDiagTailX0RatChunk000Sub001Block179Part021
    + surrogateDiagTailX0RatChunk000Sub001Block179Part022
    + surrogateDiagTailX0RatChunk000Sub001Block179Part023
    + surrogateDiagTailX0RatChunk000Sub001Block179Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block179_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block179Head + surrogateDiagTailX0RatChunk000Sub001Block179Mid + surrogateDiagTailX0RatChunk000Sub001Block179Tail =
      surrogateDiagTailX0RatChunk000Sub001Block179 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block179Head surrogateDiagTailX0RatChunk000Sub001Block179Mid surrogateDiagTailX0RatChunk000Sub001Block179Tail surrogateDiagTailX0RatChunk000Sub001Block179
  ring

def SurrogateDiagonalTailChunk000Sub001Block179HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block179HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block179Head

def SurrogateDiagonalTailChunk000Sub001Block179MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block179MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block179Mid

def SurrogateDiagonalTailChunk000Sub001Block179TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block179TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block179Tail

theorem surrogateDiagonalTailChunk000Sub001Block179_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block179HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block179MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block179TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block179Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block179 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block179HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block179MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block179TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block179Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block179_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
