import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [1,2). -/

/-- Block 001 covers tail-support indices [5025,5050) and q from 8313 to 8353. -/

def TailChunk000Sub001Block001Part000SupportExplicit : Finset ℕ :=
  ([8313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part000 : ℚ :=
  (315457025225 : ℚ) / 601957147613331456

def SurrogateDiagonalTailChunk000Sub001Block001Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8313
    = surrogateDiagTailX0RatChunk000Sub001Block001Part000

theorem surrogateDiagonalTailChunk000Sub001Block001Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part000] using hcert

def TailChunk000Sub001Block001Part001SupportExplicit : Finset ℕ :=
  ([8314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part001 : ℚ :=
  (270010140625 : ℚ) / 186495786009422112

def SurrogateDiagonalTailChunk000Sub001Block001Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8314
    = surrogateDiagTailX0RatChunk000Sub001Block001Part001

theorem surrogateDiagonalTailChunk000Sub001Block001Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part001] using hcert

def TailChunk000Sub001Block001Part002SupportExplicit : Finset ℕ :=
  ([8315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part002 : ℚ :=
  (8108808925 : ℚ) / 76315179139191072

def SurrogateDiagonalTailChunk000Sub001Block001Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8315
    = surrogateDiagTailX0RatChunk000Sub001Block001Part002

theorem surrogateDiagonalTailChunk000Sub001Block001Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part002] using hcert

def TailChunk000Sub001Block001Part003SupportExplicit : Finset ℕ :=
  ([8317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block001Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8317
    = surrogateDiagTailX0RatChunk000Sub001Block001Part003

theorem surrogateDiagonalTailChunk000Sub001Block001Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part003] using hcert

def TailChunk000Sub001Block001Part004SupportExplicit : Finset ℕ :=
  ([8318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part004 : ℚ :=
  (270270015625 : ℚ) / 186855036155334162

def SurrogateDiagonalTailChunk000Sub001Block001Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8318
    = surrogateDiagTailX0RatChunk000Sub001Block001Part004

theorem surrogateDiagonalTailChunk000Sub001Block001Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part004] using hcert

def TailChunk000Sub001Block001Part005SupportExplicit : Finset ℕ :=
  ([8319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part005 : ℚ :=
  (238389607825 : ℚ) / 506792467367588352

def SurrogateDiagonalTailChunk000Sub001Block001Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8319
    = surrogateDiagTailX0RatChunk000Sub001Block001Part005

theorem surrogateDiagonalTailChunk000Sub001Block001Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part005] using hcert

def TailChunk000Sub001Block001Part006SupportExplicit : Finset ℕ :=
  ([8321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part006 : ℚ :=
  (21574946425 : ℚ) / 3609253382208454656

def SurrogateDiagonalTailChunk000Sub001Block001Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8321
    = surrogateDiagTailX0RatChunk000Sub001Block001Part006

theorem surrogateDiagonalTailChunk000Sub001Block001Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part006] using hcert

def TailChunk000Sub001Block001Part007SupportExplicit : Finset ℕ :=
  ([8322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part007 : ℚ :=
  (43735101325 : ℚ) / 6270386954305536

def SurrogateDiagonalTailChunk000Sub001Block001Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8322
    = surrogateDiagTailX0RatChunk000Sub001Block001Part007

theorem surrogateDiagonalTailChunk000Sub001Block001Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part007] using hcert

def TailChunk000Sub001Block001Part008SupportExplicit : Finset ℕ :=
  ([8323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part008 : ℚ :=
  (17435618269 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block001Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8323
    = surrogateDiagTailX0RatChunk000Sub001Block001Part008

theorem surrogateDiagonalTailChunk000Sub001Block001Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part008] using hcert

def TailChunk000Sub001Block001Part009SupportExplicit : Finset ℕ :=
  ([8326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part009 : ℚ :=
  (20836092419 : ℚ) / 12298088053785600

def SurrogateDiagonalTailChunk000Sub001Block001Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8326
    = surrogateDiagTailX0RatChunk000Sub001Block001Part009

theorem surrogateDiagonalTailChunk000Sub001Block001Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part009] using hcert

def TailChunk000Sub001Block001Part010SupportExplicit : Finset ℕ :=
  ([8327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part010 : ℚ :=
  (1444991713 : ℚ) / 46674104282265600

def SurrogateDiagonalTailChunk000Sub001Block001Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8327
    = surrogateDiagTailX0RatChunk000Sub001Block001Part010

theorem surrogateDiagonalTailChunk000Sub001Block001Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part010] using hcert

def TailChunk000Sub001Block001Part011SupportExplicit : Finset ℕ :=
  ([8329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block001Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8329
    = surrogateDiagTailX0RatChunk000Sub001Block001Part011

theorem surrogateDiagonalTailChunk000Sub001Block001Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part011] using hcert

def TailChunk000Sub001Block001Part012SupportExplicit : Finset ℕ :=
  ([8331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part012 : ℚ :=
  (120565279525 : ℚ) / 593970255726845952

def SurrogateDiagonalTailChunk000Sub001Block001Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8331
    = surrogateDiagTailX0RatChunk000Sub001Block001Part012

theorem surrogateDiagonalTailChunk000Sub001Block001Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part012] using hcert

def TailChunk000Sub001Block001Part013SupportExplicit : Finset ℕ :=
  ([8333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part013 : ℚ :=
  (152281283 : ℚ) / 7249206863462400

def SurrogateDiagonalTailChunk000Sub001Block001Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8333
    = surrogateDiagTailX0RatChunk000Sub001Block001Part013

theorem surrogateDiagonalTailChunk000Sub001Block001Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part013] using hcert

def TailChunk000Sub001Block001Part014SupportExplicit : Finset ℕ :=
  ([8335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part014 : ℚ :=
  (148773167325 : ℚ) / 234826723089000448

def SurrogateDiagonalTailChunk000Sub001Block001Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8335
    = surrogateDiagTailX0RatChunk000Sub001Block001Part014

theorem surrogateDiagonalTailChunk000Sub001Block001Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part014] using hcert

def TailChunk000Sub001Block001Part015SupportExplicit : Finset ℕ :=
  ([8337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part015 : ℚ :=
  (1993688602525 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub001Block001Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8337
    = surrogateDiagTailX0RatChunk000Sub001Block001Part015

theorem surrogateDiagonalTailChunk000Sub001Block001Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part015] using hcert

def TailChunk000Sub001Block001Part016SupportExplicit : Finset ℕ :=
  ([8338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part016 : ℚ :=
  (15101038571 : ℚ) / 4083984124698240

def SurrogateDiagonalTailChunk000Sub001Block001Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8338
    = surrogateDiagTailX0RatChunk000Sub001Block001Part016

theorem surrogateDiagonalTailChunk000Sub001Block001Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part016] using hcert

def TailChunk000Sub001Block001Part017SupportExplicit : Finset ℕ :=
  ([8339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part017 : ℚ :=
  (33047186861 : ℚ) / 83587443157002240

def SurrogateDiagonalTailChunk000Sub001Block001Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8339
    = surrogateDiagTailX0RatChunk000Sub001Block001Part017

theorem surrogateDiagonalTailChunk000Sub001Block001Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part017] using hcert

def TailChunk000Sub001Block001Part018SupportExplicit : Finset ℕ :=
  ([8341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part018 : ℚ :=
  (4023020805325 : ℚ) / 9660805115648035968

def SurrogateDiagonalTailChunk000Sub001Block001Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8341
    = surrogateDiagTailX0RatChunk000Sub001Block001Part018

theorem surrogateDiagonalTailChunk000Sub001Block001Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part018] using hcert

def TailChunk000Sub001Block001Part019SupportExplicit : Finset ℕ :=
  ([8342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part019 : ℚ :=
  (2074190158975 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub001Block001Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8342
    = surrogateDiagTailX0RatChunk000Sub001Block001Part019

theorem surrogateDiagonalTailChunk000Sub001Block001Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part019] using hcert

def TailChunk000Sub001Block001Part020SupportExplicit : Finset ℕ :=
  ([8345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part020 : ℚ :=
  (1878667775 : ℚ) / 2972455828291584

def SurrogateDiagonalTailChunk000Sub001Block001Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8345
    = surrogateDiagTailX0RatChunk000Sub001Block001Part020

theorem surrogateDiagonalTailChunk000Sub001Block001Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part020] using hcert

def TailChunk000Sub001Block001Part021SupportExplicit : Finset ℕ :=
  ([8346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part021 : ℚ :=
  (22467903125 : ℚ) / 2181996498917376

def SurrogateDiagonalTailChunk000Sub001Block001Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8346
    = surrogateDiagTailX0RatChunk000Sub001Block001Part021

theorem surrogateDiagonalTailChunk000Sub001Block001Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part021] using hcert

def TailChunk000Sub001Block001Part022SupportExplicit : Finset ℕ :=
  ([8347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part022 : ℚ :=
  (159291451303 : ℚ) / 377877558735667200

def SurrogateDiagonalTailChunk000Sub001Block001Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8347
    = surrogateDiagTailX0RatChunk000Sub001Block001Part022

theorem surrogateDiagonalTailChunk000Sub001Block001Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part022] using hcert

def TailChunk000Sub001Block001Part023SupportExplicit : Finset ℕ :=
  ([8351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part023 : ℚ :=
  (192542258975 : ℚ) / 363466489931513856

def SurrogateDiagonalTailChunk000Sub001Block001Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8351
    = surrogateDiagTailX0RatChunk000Sub001Block001Part023

theorem surrogateDiagonalTailChunk000Sub001Block001Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part023] using hcert

def TailChunk000Sub001Block001Part024SupportExplicit : Finset ℕ :=
  ([8353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block001Part024 : ℚ :=
  (1090197015625 : ℚ) / 3041787075053617152

def SurrogateDiagonalTailChunk000Sub001Block001Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8353
    = surrogateDiagTailX0RatChunk000Sub001Block001Part024

theorem surrogateDiagonalTailChunk000Sub001Block001Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block001Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block001Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block001Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block001Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block001Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block001Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block001HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block001Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block001Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block001Part000
    + surrogateDiagTailX0RatChunk000Sub001Block001Part001
    + surrogateDiagTailX0RatChunk000Sub001Block001Part002
    + surrogateDiagTailX0RatChunk000Sub001Block001Part003
    + surrogateDiagTailX0RatChunk000Sub001Block001Part004
    + surrogateDiagTailX0RatChunk000Sub001Block001Part005
    + surrogateDiagTailX0RatChunk000Sub001Block001Part006
    + surrogateDiagTailX0RatChunk000Sub001Block001Part007
    + surrogateDiagTailX0RatChunk000Sub001Block001Part008
    + surrogateDiagTailX0RatChunk000Sub001Block001Part009

def surrogateDiagonalTailChunk000Sub001Block001MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block001Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block001Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block001Part010
    + surrogateDiagTailX0RatChunk000Sub001Block001Part011
    + surrogateDiagTailX0RatChunk000Sub001Block001Part012
    + surrogateDiagTailX0RatChunk000Sub001Block001Part013
    + surrogateDiagTailX0RatChunk000Sub001Block001Part014
    + surrogateDiagTailX0RatChunk000Sub001Block001Part015
    + surrogateDiagTailX0RatChunk000Sub001Block001Part016
    + surrogateDiagTailX0RatChunk000Sub001Block001Part017
    + surrogateDiagTailX0RatChunk000Sub001Block001Part018
    + surrogateDiagTailX0RatChunk000Sub001Block001Part019

def surrogateDiagonalTailChunk000Sub001Block001TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block001Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block001Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block001Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block001Part020
    + surrogateDiagTailX0RatChunk000Sub001Block001Part021
    + surrogateDiagTailX0RatChunk000Sub001Block001Part022
    + surrogateDiagTailX0RatChunk000Sub001Block001Part023
    + surrogateDiagTailX0RatChunk000Sub001Block001Part024

def surrogateDiagonalTailChunk000Sub001Block001Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block001HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block001MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block001TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block001 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block001Part000
    + surrogateDiagTailX0RatChunk000Sub001Block001Part001
    + surrogateDiagTailX0RatChunk000Sub001Block001Part002
    + surrogateDiagTailX0RatChunk000Sub001Block001Part003
    + surrogateDiagTailX0RatChunk000Sub001Block001Part004
    + surrogateDiagTailX0RatChunk000Sub001Block001Part005
    + surrogateDiagTailX0RatChunk000Sub001Block001Part006
    + surrogateDiagTailX0RatChunk000Sub001Block001Part007
    + surrogateDiagTailX0RatChunk000Sub001Block001Part008
    + surrogateDiagTailX0RatChunk000Sub001Block001Part009
    + surrogateDiagTailX0RatChunk000Sub001Block001Part010
    + surrogateDiagTailX0RatChunk000Sub001Block001Part011
    + surrogateDiagTailX0RatChunk000Sub001Block001Part012
    + surrogateDiagTailX0RatChunk000Sub001Block001Part013
    + surrogateDiagTailX0RatChunk000Sub001Block001Part014
    + surrogateDiagTailX0RatChunk000Sub001Block001Part015
    + surrogateDiagTailX0RatChunk000Sub001Block001Part016
    + surrogateDiagTailX0RatChunk000Sub001Block001Part017
    + surrogateDiagTailX0RatChunk000Sub001Block001Part018
    + surrogateDiagTailX0RatChunk000Sub001Block001Part019
    + surrogateDiagTailX0RatChunk000Sub001Block001Part020
    + surrogateDiagTailX0RatChunk000Sub001Block001Part021
    + surrogateDiagTailX0RatChunk000Sub001Block001Part022
    + surrogateDiagTailX0RatChunk000Sub001Block001Part023
    + surrogateDiagTailX0RatChunk000Sub001Block001Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block001_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block001Head + surrogateDiagTailX0RatChunk000Sub001Block001Mid + surrogateDiagTailX0RatChunk000Sub001Block001Tail =
      surrogateDiagTailX0RatChunk000Sub001Block001 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block001Head surrogateDiagTailX0RatChunk000Sub001Block001Mid surrogateDiagTailX0RatChunk000Sub001Block001Tail surrogateDiagTailX0RatChunk000Sub001Block001
  ring

def SurrogateDiagonalTailChunk000Sub001Block001HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block001HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block001Head

def SurrogateDiagonalTailChunk000Sub001Block001MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block001MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block001Mid

def SurrogateDiagonalTailChunk000Sub001Block001TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block001TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block001Tail

theorem surrogateDiagonalTailChunk000Sub001Block001_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block001HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block001MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block001TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block001Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block001 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block001HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block001MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block001TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block001Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block001_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
