import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [50,60). -/

/-- Block 050 covers tail-support indices [6250,6275) and q from 10329 to 10366. -/

def TailChunk000Sub001Block050Part000SupportExplicit : Finset ℕ :=
  ([10329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part000 : ℚ :=
  (212589313 : ℚ) / 1010959947399168

def SurrogateDiagonalTailChunk000Sub001Block050Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10329
    = surrogateDiagTailX0RatChunk000Sub001Block050Part000

theorem surrogateDiagonalTailChunk000Sub001Block050Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part000] using hcert

def TailChunk000Sub001Block050Part001SupportExplicit : Finset ℕ :=
  ([10330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part001 : ℚ :=
  (211034295025 : ℚ) / 121013650752012288

def SurrogateDiagonalTailChunk000Sub001Block050Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10330
    = surrogateDiagTailX0RatChunk000Sub001Block050Part001

theorem surrogateDiagonalTailChunk000Sub001Block050Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part001] using hcert

def TailChunk000Sub001Block050Part002SupportExplicit : Finset ℕ :=
  ([10331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block050Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10331
    = surrogateDiagTailX0RatChunk000Sub001Block050Part002

theorem surrogateDiagonalTailChunk000Sub001Block050Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part002] using hcert

def TailChunk000Sub001Block050Part003SupportExplicit : Finset ℕ :=
  ([10333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block050Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10333
    = surrogateDiagTailX0RatChunk000Sub001Block050Part003

theorem surrogateDiagonalTailChunk000Sub001Block050Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part003] using hcert

def TailChunk000Sub001Block050Part004SupportExplicit : Finset ℕ :=
  ([10334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part004 : ℚ :=
  (417154515625 : ℚ) / 445230056488866642

def SurrogateDiagonalTailChunk000Sub001Block050Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10334
    = surrogateDiagTailX0RatChunk000Sub001Block050Part004

theorem surrogateDiagonalTailChunk000Sub001Block050Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part004] using hcert

def TailChunk000Sub001Block050Part005SupportExplicit : Finset ℕ :=
  ([10335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part005 : ℚ :=
  (76010452325 : ℚ) / 129402873267093504

def SurrogateDiagonalTailChunk000Sub001Block050Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10335
    = surrogateDiagTailX0RatChunk000Sub001Block050Part005

theorem surrogateDiagonalTailChunk000Sub001Block050Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part005] using hcert

def TailChunk000Sub001Block050Part006SupportExplicit : Finset ℕ :=
  ([10337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block050Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10337
    = surrogateDiagTailX0RatChunk000Sub001Block050Part006

theorem surrogateDiagonalTailChunk000Sub001Block050Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part006] using hcert

def TailChunk000Sub001Block050Part007SupportExplicit : Finset ℕ :=
  ([10338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part007 : ℚ :=
  (108125 : ℚ) / 34180405056

def SurrogateDiagonalTailChunk000Sub001Block050Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10338
    = surrogateDiagTailX0RatChunk000Sub001Block050Part007

theorem surrogateDiagonalTailChunk000Sub001Block050Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part007] using hcert

def TailChunk000Sub001Block050Part008SupportExplicit : Finset ℕ :=
  ([10342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part008 : ℚ :=
  (668481025 : ℚ) / 714576982029042

def SurrogateDiagonalTailChunk000Sub001Block050Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10342
    = surrogateDiagTailX0RatChunk000Sub001Block050Part008

theorem surrogateDiagonalTailChunk000Sub001Block050Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part008] using hcert

def TailChunk000Sub001Block050Part009SupportExplicit : Finset ℕ :=
  ([10343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block050Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10343
    = surrogateDiagTailX0RatChunk000Sub001Block050Part009

theorem surrogateDiagonalTailChunk000Sub001Block050Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part009] using hcert

def TailChunk000Sub001Block050Part010SupportExplicit : Finset ℕ :=
  ([10345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part010 : ℚ :=
  (401398114775 : ℚ) / 5853814636781912064

def SurrogateDiagonalTailChunk000Sub001Block050Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10345
    = surrogateDiagTailX0RatChunk000Sub001Block050Part010

theorem surrogateDiagonalTailChunk000Sub001Block050Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part010] using hcert

def TailChunk000Sub001Block050Part011SupportExplicit : Finset ℕ :=
  ([10346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part011 : ℚ :=
  (26515715275 : ℚ) / 17801784849200832

def SurrogateDiagonalTailChunk000Sub001Block050Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10346
    = surrogateDiagTailX0RatChunk000Sub001Block050Part011

theorem surrogateDiagonalTailChunk000Sub001Block050Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part011] using hcert

def TailChunk000Sub001Block050Part012SupportExplicit : Finset ℕ :=
  ([10347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part012 : ℚ :=
  (743207781275 : ℚ) / 2827391021123518464

def SurrogateDiagonalTailChunk000Sub001Block050Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10347
    = surrogateDiagTailX0RatChunk000Sub001Block050Part012

theorem surrogateDiagonalTailChunk000Sub001Block050Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part012] using hcert

def TailChunk000Sub001Block050Part013SupportExplicit : Finset ℕ :=
  ([10349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part013 : ℚ :=
  (1282112069 : ℚ) / 528699225909441600

def SurrogateDiagonalTailChunk000Sub001Block050Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10349
    = surrogateDiagTailX0RatChunk000Sub001Block050Part013

theorem surrogateDiagonalTailChunk000Sub001Block050Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part013] using hcert

def TailChunk000Sub001Block050Part014SupportExplicit : Finset ℕ :=
  ([10351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part014 : ℚ :=
  (558062459 : ℚ) / 39045255489600000

def SurrogateDiagonalTailChunk000Sub001Block050Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10351
    = surrogateDiagTailX0RatChunk000Sub001Block050Part014

theorem surrogateDiagonalTailChunk000Sub001Block050Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part014] using hcert

def TailChunk000Sub001Block050Part015SupportExplicit : Finset ℕ :=
  ([10353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part015 : ℚ :=
  (23506468975 : ℚ) / 38678545953718272

def SurrogateDiagonalTailChunk000Sub001Block050Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10353
    = surrogateDiagTailX0RatChunk000Sub001Block050Part015

theorem surrogateDiagonalTailChunk000Sub001Block050Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part015] using hcert

def TailChunk000Sub001Block050Part016SupportExplicit : Finset ℕ :=
  ([10354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part016 : ℚ :=
  (32157375611 : ℚ) / 30759142606401600

def SurrogateDiagonalTailChunk000Sub001Block050Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10354
    = surrogateDiagTailX0RatChunk000Sub001Block050Part016

theorem surrogateDiagonalTailChunk000Sub001Block050Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part016] using hcert

def TailChunk000Sub001Block050Part017SupportExplicit : Finset ℕ :=
  ([10355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part017 : ℚ :=
  (208355230925 : ℚ) / 3047408059792490496

def SurrogateDiagonalTailChunk000Sub001Block050Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10355
    = surrogateDiagTailX0RatChunk000Sub001Block050Part017

theorem surrogateDiagonalTailChunk000Sub001Block050Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part017] using hcert

def TailChunk000Sub001Block050Part018SupportExplicit : Finset ℕ :=
  ([10357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block050Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10357
    = surrogateDiagTailX0RatChunk000Sub001Block050Part018

theorem surrogateDiagonalTailChunk000Sub001Block050Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part018] using hcert

def TailChunk000Sub001Block050Part019SupportExplicit : Finset ℕ :=
  ([10358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part019 : ℚ :=
  (419094390625 : ℚ) / 449381357622274482

def SurrogateDiagonalTailChunk000Sub001Block050Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10358
    = surrogateDiagTailX0RatChunk000Sub001Block050Part019

theorem surrogateDiagonalTailChunk000Sub001Block050Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part019] using hcert

def TailChunk000Sub001Block050Part020SupportExplicit : Finset ℕ :=
  ([10361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part020 : ℚ :=
  (241121074375 : ℚ) / 20816327599072247808

def SurrogateDiagonalTailChunk000Sub001Block050Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10361
    = surrogateDiagTailX0RatChunk000Sub001Block050Part020

theorem surrogateDiagonalTailChunk000Sub001Block050Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part020] using hcert

def TailChunk000Sub001Block050Part021SupportExplicit : Finset ℕ :=
  ([10362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part021 : ℚ :=
  (6725074061 : ℚ) / 1579624917811200

def SurrogateDiagonalTailChunk000Sub001Block050Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10362
    = surrogateDiagTailX0RatChunk000Sub001Block050Part021

theorem surrogateDiagonalTailChunk000Sub001Block050Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part021] using hcert

def TailChunk000Sub001Block050Part022SupportExplicit : Finset ℕ :=
  ([10363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part022 : ℚ :=
  (78663973 : ℚ) / 22946500651253760

def SurrogateDiagonalTailChunk000Sub001Block050Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10363
    = surrogateDiagTailX0RatChunk000Sub001Block050Part022

theorem surrogateDiagonalTailChunk000Sub001Block050Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part022] using hcert

def TailChunk000Sub001Block050Part023SupportExplicit : Finset ℕ :=
  ([10365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part023 : ℚ :=
  (51271627789 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk000Sub001Block050Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10365
    = surrogateDiagTailX0RatChunk000Sub001Block050Part023

theorem surrogateDiagonalTailChunk000Sub001Block050Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part023] using hcert

def TailChunk000Sub001Block050Part024SupportExplicit : Finset ℕ :=
  ([10366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block050Part024 : ℚ :=
  (8155343087 : ℚ) / 8067129135206400

def SurrogateDiagonalTailChunk000Sub001Block050Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10366
    = surrogateDiagTailX0RatChunk000Sub001Block050Part024

theorem surrogateDiagonalTailChunk000Sub001Block050Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block050Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block050Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block050Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block050Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block050Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block050Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block050HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block050Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block050Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block050Part000
    + surrogateDiagTailX0RatChunk000Sub001Block050Part001
    + surrogateDiagTailX0RatChunk000Sub001Block050Part002
    + surrogateDiagTailX0RatChunk000Sub001Block050Part003
    + surrogateDiagTailX0RatChunk000Sub001Block050Part004
    + surrogateDiagTailX0RatChunk000Sub001Block050Part005
    + surrogateDiagTailX0RatChunk000Sub001Block050Part006
    + surrogateDiagTailX0RatChunk000Sub001Block050Part007
    + surrogateDiagTailX0RatChunk000Sub001Block050Part008
    + surrogateDiagTailX0RatChunk000Sub001Block050Part009

def surrogateDiagonalTailChunk000Sub001Block050MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block050Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block050Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block050Part010
    + surrogateDiagTailX0RatChunk000Sub001Block050Part011
    + surrogateDiagTailX0RatChunk000Sub001Block050Part012
    + surrogateDiagTailX0RatChunk000Sub001Block050Part013
    + surrogateDiagTailX0RatChunk000Sub001Block050Part014
    + surrogateDiagTailX0RatChunk000Sub001Block050Part015
    + surrogateDiagTailX0RatChunk000Sub001Block050Part016
    + surrogateDiagTailX0RatChunk000Sub001Block050Part017
    + surrogateDiagTailX0RatChunk000Sub001Block050Part018
    + surrogateDiagTailX0RatChunk000Sub001Block050Part019

def surrogateDiagonalTailChunk000Sub001Block050TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block050Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block050Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block050Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block050Part020
    + surrogateDiagTailX0RatChunk000Sub001Block050Part021
    + surrogateDiagTailX0RatChunk000Sub001Block050Part022
    + surrogateDiagTailX0RatChunk000Sub001Block050Part023
    + surrogateDiagTailX0RatChunk000Sub001Block050Part024

def surrogateDiagonalTailChunk000Sub001Block050Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block050HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block050MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block050TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block050 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block050Part000
    + surrogateDiagTailX0RatChunk000Sub001Block050Part001
    + surrogateDiagTailX0RatChunk000Sub001Block050Part002
    + surrogateDiagTailX0RatChunk000Sub001Block050Part003
    + surrogateDiagTailX0RatChunk000Sub001Block050Part004
    + surrogateDiagTailX0RatChunk000Sub001Block050Part005
    + surrogateDiagTailX0RatChunk000Sub001Block050Part006
    + surrogateDiagTailX0RatChunk000Sub001Block050Part007
    + surrogateDiagTailX0RatChunk000Sub001Block050Part008
    + surrogateDiagTailX0RatChunk000Sub001Block050Part009
    + surrogateDiagTailX0RatChunk000Sub001Block050Part010
    + surrogateDiagTailX0RatChunk000Sub001Block050Part011
    + surrogateDiagTailX0RatChunk000Sub001Block050Part012
    + surrogateDiagTailX0RatChunk000Sub001Block050Part013
    + surrogateDiagTailX0RatChunk000Sub001Block050Part014
    + surrogateDiagTailX0RatChunk000Sub001Block050Part015
    + surrogateDiagTailX0RatChunk000Sub001Block050Part016
    + surrogateDiagTailX0RatChunk000Sub001Block050Part017
    + surrogateDiagTailX0RatChunk000Sub001Block050Part018
    + surrogateDiagTailX0RatChunk000Sub001Block050Part019
    + surrogateDiagTailX0RatChunk000Sub001Block050Part020
    + surrogateDiagTailX0RatChunk000Sub001Block050Part021
    + surrogateDiagTailX0RatChunk000Sub001Block050Part022
    + surrogateDiagTailX0RatChunk000Sub001Block050Part023
    + surrogateDiagTailX0RatChunk000Sub001Block050Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block050_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block050Head + surrogateDiagTailX0RatChunk000Sub001Block050Mid + surrogateDiagTailX0RatChunk000Sub001Block050Tail =
      surrogateDiagTailX0RatChunk000Sub001Block050 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block050Head surrogateDiagTailX0RatChunk000Sub001Block050Mid surrogateDiagTailX0RatChunk000Sub001Block050Tail surrogateDiagTailX0RatChunk000Sub001Block050
  ring

def SurrogateDiagonalTailChunk000Sub001Block050HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block050HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block050Head

def SurrogateDiagonalTailChunk000Sub001Block050MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block050MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block050Mid

def SurrogateDiagonalTailChunk000Sub001Block050TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block050TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block050Tail

theorem surrogateDiagonalTailChunk000Sub001Block050_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block050HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block050MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block050TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block050Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block050 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block050HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block050MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block050TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block050Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block050_eq_head_add_mid_add_tail

/-- Block 051 covers tail-support indices [6275,6300) and q from 10367 to 10405. -/

def TailChunk000Sub001Block051Part000SupportExplicit : Finset ℕ :=
  ([10367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part000 : ℚ :=
  (916467433 : ℚ) / 34551444459110400

def SurrogateDiagonalTailChunk000Sub001Block051Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10367
    = surrogateDiagTailX0RatChunk000Sub001Block051Part000

theorem surrogateDiagonalTailChunk000Sub001Block051Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part000] using hcert

def TailChunk000Sub001Block051Part001SupportExplicit : Finset ℕ :=
  ([10369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block051Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10369
    = surrogateDiagTailX0RatChunk000Sub001Block051Part001

theorem surrogateDiagonalTailChunk000Sub001Block051Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part001] using hcert

def TailChunk000Sub001Block051Part002SupportExplicit : Finset ℕ :=
  ([10370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part002 : ℚ :=
  (15766845563 : ℚ) / 7249206863462400

def SurrogateDiagonalTailChunk000Sub001Block051Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10370
    = surrogateDiagTailX0RatChunk000Sub001Block051Part002

theorem surrogateDiagonalTailChunk000Sub001Block051Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part002] using hcert

def TailChunk000Sub001Block051Part003SupportExplicit : Finset ℕ :=
  ([10371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part003 : ℚ :=
  (746659090475 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk000Sub001Block051Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10371
    = surrogateDiagTailX0RatChunk000Sub001Block051Part003

theorem surrogateDiagonalTailChunk000Sub001Block051Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part003] using hcert

def TailChunk000Sub001Block051Part004SupportExplicit : Finset ℕ :=
  ([10373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part004 : ℚ :=
  (690606121 : ℚ) / 23992611962880000

def SurrogateDiagonalTailChunk000Sub001Block051Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10373
    = surrogateDiagTailX0RatChunk000Sub001Block051Part004

theorem surrogateDiagonalTailChunk000Sub001Block051Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part004] using hcert

def TailChunk000Sub001Block051Part005SupportExplicit : Finset ℕ :=
  ([10374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part005 : ℚ :=
  (831692489125 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub001Block051Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10374
    = surrogateDiagTailX0RatChunk000Sub001Block051Part005

theorem surrogateDiagonalTailChunk000Sub001Block051Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part005] using hcert

def TailChunk000Sub001Block051Part006SupportExplicit : Finset ℕ :=
  ([10378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part006 : ℚ :=
  (420714390625 : ℚ) / 452862893616789792

def SurrogateDiagonalTailChunk000Sub001Block051Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10378
    = surrogateDiagTailX0RatChunk000Sub001Block051Part006

theorem surrogateDiagonalTailChunk000Sub001Block051Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part006] using hcert

def TailChunk000Sub001Block051Part007SupportExplicit : Finset ℕ :=
  ([10379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part007 : ℚ :=
  (62955213025 : ℚ) / 26812372978696716288

def SurrogateDiagonalTailChunk000Sub001Block051Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10379
    = surrogateDiagTailX0RatChunk000Sub001Block051Part007

theorem surrogateDiagonalTailChunk000Sub001Block051Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part007] using hcert

def TailChunk000Sub001Block051Part008SupportExplicit : Finset ℕ :=
  ([10381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part008 : ℚ :=
  (7657789825 : ℚ) / 289488232847915712

def SurrogateDiagonalTailChunk000Sub001Block051Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10381
    = surrogateDiagTailX0RatChunk000Sub001Block051Part008

theorem surrogateDiagonalTailChunk000Sub001Block051Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part008] using hcert

def TailChunk000Sub001Block051Part009SupportExplicit : Finset ℕ :=
  ([10382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part009 : ℚ :=
  (538328115525 : ℚ) / 514301438174304256

def SurrogateDiagonalTailChunk000Sub001Block051Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10382
    = surrogateDiagTailX0RatChunk000Sub001Block051Part009

theorem surrogateDiagonalTailChunk000Sub001Block051Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part009] using hcert

def TailChunk000Sub001Block051Part010SupportExplicit : Finset ℕ :=
  ([10383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part010 : ℚ :=
  (748850101 : ℚ) / 5733914816052480

def SurrogateDiagonalTailChunk000Sub001Block051Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10383
    = surrogateDiagTailX0RatChunk000Sub001Block051Part010

theorem surrogateDiagonalTailChunk000Sub001Block051Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part010] using hcert

def TailChunk000Sub001Block051Part011SupportExplicit : Finset ℕ :=
  ([10385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part011 : ℚ :=
  (11380300249 : ℚ) / 131179605907046400

def SurrogateDiagonalTailChunk000Sub001Block051Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10385
    = surrogateDiagTailX0RatChunk000Sub001Block051Part011

theorem surrogateDiagonalTailChunk000Sub001Block051Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part011] using hcert

def TailChunk000Sub001Block051Part012SupportExplicit : Finset ℕ :=
  ([10387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part012 : ℚ :=
  (153916609775 : ℚ) / 5071563244695453696

def SurrogateDiagonalTailChunk000Sub001Block051Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10387
    = surrogateDiagTailX0RatChunk000Sub001Block051Part012

theorem surrogateDiagonalTailChunk000Sub001Block051Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part012] using hcert

def TailChunk000Sub001Block051Part013SupportExplicit : Finset ℕ :=
  ([10389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part013 : ℚ :=
  (374857675475 : ℚ) / 2873591961014228544

def SurrogateDiagonalTailChunk000Sub001Block051Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10389
    = surrogateDiagTailX0RatChunk000Sub001Block051Part013

theorem surrogateDiagonalTailChunk000Sub001Block051Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part013] using hcert

def TailChunk000Sub001Block051Part014SupportExplicit : Finset ℕ :=
  ([10390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part014 : ℚ :=
  (674162180375 : ℚ) / 371557680080200704

def SurrogateDiagonalTailChunk000Sub001Block051Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10390
    = surrogateDiagTailX0RatChunk000Sub001Block051Part014

theorem surrogateDiagonalTailChunk000Sub001Block051Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part014] using hcert

def TailChunk000Sub001Block051Part015SupportExplicit : Finset ℕ :=
  ([10391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block051Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10391
    = surrogateDiagTailX0RatChunk000Sub001Block051Part015

theorem surrogateDiagonalTailChunk000Sub001Block051Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part015] using hcert

def TailChunk000Sub001Block051Part016SupportExplicit : Finset ℕ :=
  ([10393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part016 : ℚ :=
  (21630470975 : ℚ) / 2916066764637660816

def SurrogateDiagonalTailChunk000Sub001Block051Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10393
    = surrogateDiagTailX0RatChunk000Sub001Block051Part016

theorem surrogateDiagonalTailChunk000Sub001Block051Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part016] using hcert

def TailChunk000Sub001Block051Part017SupportExplicit : Finset ℕ :=
  ([10394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part017 : ℚ :=
  (422012640625 : ℚ) / 455662655876473632

def SurrogateDiagonalTailChunk000Sub001Block051Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10394
    = surrogateDiagTailX0RatChunk000Sub001Block051Part017

theorem surrogateDiagonalTailChunk000Sub001Block051Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part017] using hcert

def TailChunk000Sub001Block051Part018SupportExplicit : Finset ℕ :=
  ([10397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part018 : ℚ :=
  (2622721 : ℚ) / 682931567001600

def SurrogateDiagonalTailChunk000Sub001Block051Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10397
    = surrogateDiagTailX0RatChunk000Sub001Block051Part018

theorem surrogateDiagonalTailChunk000Sub001Block051Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part018] using hcert

def TailChunk000Sub001Block051Part019SupportExplicit : Finset ℕ :=
  ([10398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part019 : ℚ :=
  (112555875 : ℚ) / 35995776123904

def SurrogateDiagonalTailChunk000Sub001Block051Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10398
    = surrogateDiagTailX0RatChunk000Sub001Block051Part019

theorem surrogateDiagonalTailChunk000Sub001Block051Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part019] using hcert

def TailChunk000Sub001Block051Part020SupportExplicit : Finset ℕ :=
  ([10399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block051Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10399
    = surrogateDiagTailX0RatChunk000Sub001Block051Part020

theorem surrogateDiagonalTailChunk000Sub001Block051Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part020] using hcert

def TailChunk000Sub001Block051Part021SupportExplicit : Finset ℕ :=
  ([10401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part021 : ℚ :=
  (375723675425 : ℚ) / 2886895605275041344

def SurrogateDiagonalTailChunk000Sub001Block051Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10401
    = surrogateDiagTailX0RatChunk000Sub001Block051Part021

theorem surrogateDiagonalTailChunk000Sub001Block051Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part021] using hcert

def TailChunk000Sub001Block051Part022SupportExplicit : Finset ℕ :=
  ([10402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part022 : ℚ :=
  (11487235975 : ℚ) / 7796091657590208

def SurrogateDiagonalTailChunk000Sub001Block051Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10402
    = surrogateDiagTailX0RatChunk000Sub001Block051Part022

theorem surrogateDiagonalTailChunk000Sub001Block051Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part022] using hcert

def TailChunk000Sub001Block051Part023SupportExplicit : Finset ℕ :=
  ([10403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part023 : ℚ :=
  (2498774623 : ℚ) / 1082648646432000000

def SurrogateDiagonalTailChunk000Sub001Block051Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10403
    = surrogateDiagTailX0RatChunk000Sub001Block051Part023

theorem surrogateDiagonalTailChunk000Sub001Block051Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part023] using hcert

def TailChunk000Sub001Block051Part024SupportExplicit : Finset ℕ :=
  ([10405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block051Part024 : ℚ :=
  (21677693629 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk000Sub001Block051Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10405
    = surrogateDiagTailX0RatChunk000Sub001Block051Part024

theorem surrogateDiagonalTailChunk000Sub001Block051Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block051Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block051Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block051Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block051Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block051Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block051Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block051HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block051Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block051Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block051Part000
    + surrogateDiagTailX0RatChunk000Sub001Block051Part001
    + surrogateDiagTailX0RatChunk000Sub001Block051Part002
    + surrogateDiagTailX0RatChunk000Sub001Block051Part003
    + surrogateDiagTailX0RatChunk000Sub001Block051Part004
    + surrogateDiagTailX0RatChunk000Sub001Block051Part005
    + surrogateDiagTailX0RatChunk000Sub001Block051Part006
    + surrogateDiagTailX0RatChunk000Sub001Block051Part007
    + surrogateDiagTailX0RatChunk000Sub001Block051Part008
    + surrogateDiagTailX0RatChunk000Sub001Block051Part009

def surrogateDiagonalTailChunk000Sub001Block051MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block051Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block051Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block051Part010
    + surrogateDiagTailX0RatChunk000Sub001Block051Part011
    + surrogateDiagTailX0RatChunk000Sub001Block051Part012
    + surrogateDiagTailX0RatChunk000Sub001Block051Part013
    + surrogateDiagTailX0RatChunk000Sub001Block051Part014
    + surrogateDiagTailX0RatChunk000Sub001Block051Part015
    + surrogateDiagTailX0RatChunk000Sub001Block051Part016
    + surrogateDiagTailX0RatChunk000Sub001Block051Part017
    + surrogateDiagTailX0RatChunk000Sub001Block051Part018
    + surrogateDiagTailX0RatChunk000Sub001Block051Part019

def surrogateDiagonalTailChunk000Sub001Block051TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block051Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block051Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block051Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block051Part020
    + surrogateDiagTailX0RatChunk000Sub001Block051Part021
    + surrogateDiagTailX0RatChunk000Sub001Block051Part022
    + surrogateDiagTailX0RatChunk000Sub001Block051Part023
    + surrogateDiagTailX0RatChunk000Sub001Block051Part024

def surrogateDiagonalTailChunk000Sub001Block051Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block051HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block051MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block051TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block051 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block051Part000
    + surrogateDiagTailX0RatChunk000Sub001Block051Part001
    + surrogateDiagTailX0RatChunk000Sub001Block051Part002
    + surrogateDiagTailX0RatChunk000Sub001Block051Part003
    + surrogateDiagTailX0RatChunk000Sub001Block051Part004
    + surrogateDiagTailX0RatChunk000Sub001Block051Part005
    + surrogateDiagTailX0RatChunk000Sub001Block051Part006
    + surrogateDiagTailX0RatChunk000Sub001Block051Part007
    + surrogateDiagTailX0RatChunk000Sub001Block051Part008
    + surrogateDiagTailX0RatChunk000Sub001Block051Part009
    + surrogateDiagTailX0RatChunk000Sub001Block051Part010
    + surrogateDiagTailX0RatChunk000Sub001Block051Part011
    + surrogateDiagTailX0RatChunk000Sub001Block051Part012
    + surrogateDiagTailX0RatChunk000Sub001Block051Part013
    + surrogateDiagTailX0RatChunk000Sub001Block051Part014
    + surrogateDiagTailX0RatChunk000Sub001Block051Part015
    + surrogateDiagTailX0RatChunk000Sub001Block051Part016
    + surrogateDiagTailX0RatChunk000Sub001Block051Part017
    + surrogateDiagTailX0RatChunk000Sub001Block051Part018
    + surrogateDiagTailX0RatChunk000Sub001Block051Part019
    + surrogateDiagTailX0RatChunk000Sub001Block051Part020
    + surrogateDiagTailX0RatChunk000Sub001Block051Part021
    + surrogateDiagTailX0RatChunk000Sub001Block051Part022
    + surrogateDiagTailX0RatChunk000Sub001Block051Part023
    + surrogateDiagTailX0RatChunk000Sub001Block051Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block051_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block051Head + surrogateDiagTailX0RatChunk000Sub001Block051Mid + surrogateDiagTailX0RatChunk000Sub001Block051Tail =
      surrogateDiagTailX0RatChunk000Sub001Block051 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block051Head surrogateDiagTailX0RatChunk000Sub001Block051Mid surrogateDiagTailX0RatChunk000Sub001Block051Tail surrogateDiagTailX0RatChunk000Sub001Block051
  ring

def SurrogateDiagonalTailChunk000Sub001Block051HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block051HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block051Head

def SurrogateDiagonalTailChunk000Sub001Block051MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block051MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block051Mid

def SurrogateDiagonalTailChunk000Sub001Block051TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block051TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block051Tail

theorem surrogateDiagonalTailChunk000Sub001Block051_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block051HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block051MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block051TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block051Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block051 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block051HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block051MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block051TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block051Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block051_eq_head_add_mid_add_tail

/-- Block 052 covers tail-support indices [6300,6325) and q from 10407 to 10447. -/

def TailChunk000Sub001Block052Part000SupportExplicit : Finset ℕ :=
  ([10407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part000 : ℚ :=
  (11754907825 : ℚ) / 90423897598647072

def SurrogateDiagonalTailChunk000Sub001Block052Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10407
    = surrogateDiagTailX0RatChunk000Sub001Block052Part000

theorem surrogateDiagonalTailChunk000Sub001Block052Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part000] using hcert

def TailChunk000Sub001Block052Part001SupportExplicit : Finset ℕ :=
  ([10409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part001 : ℚ :=
  (23096986675 : ℚ) / 877878864059558976

def SurrogateDiagonalTailChunk000Sub001Block052Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10409
    = surrogateDiagTailX0RatChunk000Sub001Block052Part001

theorem surrogateDiagonalTailChunk000Sub001Block052Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part001] using hcert

def TailChunk000Sub001Block052Part002SupportExplicit : Finset ℕ :=
  ([10410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part002 : ℚ :=
  (900542696275 : ℚ) / 146788219290943488

def SurrogateDiagonalTailChunk000Sub001Block052Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10410
    = surrogateDiagTailX0RatChunk000Sub001Block052Part002

theorem surrogateDiagonalTailChunk000Sub001Block052Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part002] using hcert

def TailChunk000Sub001Block052Part003SupportExplicit : Finset ℕ :=
  ([10411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part003 : ℚ :=
  (40194161625 : ℚ) / 8415304518768695296

def SurrogateDiagonalTailChunk000Sub001Block052Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10411
    = surrogateDiagTailX0RatChunk000Sub001Block052Part003

theorem surrogateDiagonalTailChunk000Sub001Block052Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part003] using hcert

def TailChunk000Sub001Block052Part004SupportExplicit : Finset ℕ :=
  ([10414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part004 : ℚ :=
  (31814821 : ℚ) / 1008391141900800

def SurrogateDiagonalTailChunk000Sub001Block052Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10414
    = surrogateDiagTailX0RatChunk000Sub001Block052Part004

theorem surrogateDiagonalTailChunk000Sub001Block052Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part004] using hcert

def TailChunk000Sub001Block052Part005SupportExplicit : Finset ℕ :=
  ([10415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part005 : ℚ :=
  (180994210675 : ℚ) / 4009299226156210176

def SurrogateDiagonalTailChunk000Sub001Block052Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10415
    = surrogateDiagTailX0RatChunk000Sub001Block052Part005

theorem surrogateDiagonalTailChunk000Sub001Block052Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part005] using hcert

def TailChunk000Sub001Block052Part006SupportExplicit : Finset ℕ :=
  ([10417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part006 : ℚ :=
  (3917935323 : ℚ) / 13350580366423520

def SurrogateDiagonalTailChunk000Sub001Block052Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10417
    = surrogateDiagTailX0RatChunk000Sub001Block052Part006

theorem surrogateDiagonalTailChunk000Sub001Block052Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part006] using hcert

def TailChunk000Sub001Block052Part007SupportExplicit : Finset ℕ :=
  ([10418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part007 : ℚ :=
  (423963765625 : ℚ) / 459886615189811712

def SurrogateDiagonalTailChunk000Sub001Block052Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10418
    = surrogateDiagTailX0RatChunk000Sub001Block052Part007

theorem surrogateDiagonalTailChunk000Sub001Block052Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part007] using hcert

def TailChunk000Sub001Block052Part008SupportExplicit : Finset ℕ :=
  ([10419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part008 : ℚ :=
  (35029952143 : ℚ) / 47446327368000000

def SurrogateDiagonalTailChunk000Sub001Block052Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10419
    = surrogateDiagTailX0RatChunk000Sub001Block052Part008

theorem surrogateDiagonalTailChunk000Sub001Block052Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part008] using hcert

def TailChunk000Sub001Block052Part009SupportExplicit : Finset ℕ :=
  ([10421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part009 : ℚ :=
  (1027066696625 : ℚ) / 3831432931398647808

def SurrogateDiagonalTailChunk000Sub001Block052Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10421
    = surrogateDiagTailX0RatChunk000Sub001Block052Part009

theorem surrogateDiagonalTailChunk000Sub001Block052Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part009] using hcert

def TailChunk000Sub001Block052Part010SupportExplicit : Finset ℕ :=
  ([10423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part010 : ℚ :=
  (299982111575 : ℚ) / 882614545103978496

def SurrogateDiagonalTailChunk000Sub001Block052Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10423
    = surrogateDiagTailX0RatChunk000Sub001Block052Part010

theorem surrogateDiagonalTailChunk000Sub001Block052Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part010] using hcert

def TailChunk000Sub001Block052Part011SupportExplicit : Finset ℕ :=
  ([10426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part011 : ℚ :=
  (31281129971 : ℚ) / 26547388416000000

def SurrogateDiagonalTailChunk000Sub001Block052Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10426
    = surrogateDiagTailX0RatChunk000Sub001Block052Part011

theorem surrogateDiagonalTailChunk000Sub001Block052Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part011] using hcert

def TailChunk000Sub001Block052Part012SupportExplicit : Finset ℕ :=
  ([10427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part012 : ℚ :=
  (1698786390625 : ℚ) / 7386483804222182322

def SurrogateDiagonalTailChunk000Sub001Block052Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10427
    = surrogateDiagTailX0RatChunk000Sub001Block052Part012

theorem surrogateDiagonalTailChunk000Sub001Block052Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part012] using hcert

def TailChunk000Sub001Block052Part013SupportExplicit : Finset ℕ :=
  ([10429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part013 : ℚ :=
  (1699438140625 : ℚ) / 7392153176544467232

def SurrogateDiagonalTailChunk000Sub001Block052Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10429
    = surrogateDiagTailX0RatChunk000Sub001Block052Part013

theorem surrogateDiagonalTailChunk000Sub001Block052Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part013] using hcert

def TailChunk000Sub001Block052Part014SupportExplicit : Finset ℕ :=
  ([10430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part014 : ℚ :=
  (4436454175 : ℚ) / 1554815000659968

def SurrogateDiagonalTailChunk000Sub001Block052Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10430
    = surrogateDiagTailX0RatChunk000Sub001Block052Part014

theorem surrogateDiagonalTailChunk000Sub001Block052Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part014] using hcert

def TailChunk000Sub001Block052Part015SupportExplicit : Finset ℕ :=
  ([10433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part015 : ℚ :=
  (1700742015625 : ℚ) / 7403501711284764672

def SurrogateDiagonalTailChunk000Sub001Block052Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10433
    = surrogateDiagTailX0RatChunk000Sub001Block052Part015

theorem surrogateDiagonalTailChunk000Sub001Block052Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part015] using hcert

def TailChunk000Sub001Block052Part016SupportExplicit : Finset ℕ :=
  ([10434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part016 : ℚ :=
  (1077682153225 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub001Block052Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10434
    = surrogateDiagTailX0RatChunk000Sub001Block052Part016

theorem surrogateDiagonalTailChunk000Sub001Block052Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part016] using hcert

def TailChunk000Sub001Block052Part017SupportExplicit : Finset ℕ :=
  ([10435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part017 : ℚ :=
  (4625043733525 : ℚ) / 12120597810077288448

def SurrogateDiagonalTailChunk000Sub001Block052Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10435
    = surrogateDiagTailX0RatChunk000Sub001Block052Part017

theorem surrogateDiagonalTailChunk000Sub001Block052Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part017] using hcert

def TailChunk000Sub001Block052Part018SupportExplicit : Finset ℕ :=
  ([10438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part018 : ℚ :=
  (795628993475 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk000Sub001Block052Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10438
    = surrogateDiagTailX0RatChunk000Sub001Block052Part018

theorem surrogateDiagonalTailChunk000Sub001Block052Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part018] using hcert

def TailChunk000Sub001Block052Part019SupportExplicit : Finset ℕ :=
  ([10439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part019 : ℚ :=
  (204665164231 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk000Sub001Block052Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10439
    = surrogateDiagTailX0RatChunk000Sub001Block052Part019

theorem surrogateDiagonalTailChunk000Sub001Block052Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part019] using hcert

def TailChunk000Sub001Block052Part020SupportExplicit : Finset ℕ :=
  ([10441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part020 : ℚ :=
  (6567056694775 : ℚ) / 26981402387623477248

def SurrogateDiagonalTailChunk000Sub001Block052Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10441
    = surrogateDiagTailX0RatChunk000Sub001Block052Part020

theorem surrogateDiagonalTailChunk000Sub001Block052Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part020] using hcert

def TailChunk000Sub001Block052Part021SupportExplicit : Finset ℕ :=
  ([10442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part021 : ℚ :=
  (539747006325 : ℚ) / 509366154172475776

def SurrogateDiagonalTailChunk000Sub001Block052Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10442
    = surrogateDiagTailX0RatChunk000Sub001Block052Part021

theorem surrogateDiagonalTailChunk000Sub001Block052Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part021] using hcert

def TailChunk000Sub001Block052Part022SupportExplicit : Finset ℕ :=
  ([10445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part022 : ℚ :=
  (4633914318475 : ℚ) / 12167148300214468608

def SurrogateDiagonalTailChunk000Sub001Block052Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10445
    = surrogateDiagTailX0RatChunk000Sub001Block052Part022

theorem surrogateDiagonalTailChunk000Sub001Block052Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part022] using hcert

def TailChunk000Sub001Block052Part023SupportExplicit : Finset ℕ :=
  ([10446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part023 : ℚ :=
  (1514633 : ℚ) / 488872627200

def SurrogateDiagonalTailChunk000Sub001Block052Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10446
    = surrogateDiagTailX0RatChunk000Sub001Block052Part023

theorem surrogateDiagonalTailChunk000Sub001Block052Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part023] using hcert

def TailChunk000Sub001Block052Part024SupportExplicit : Finset ℕ :=
  ([10447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block052Part024 : ℚ :=
  (36910928869 : ℚ) / 147513218472345600

def SurrogateDiagonalTailChunk000Sub001Block052Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10447
    = surrogateDiagTailX0RatChunk000Sub001Block052Part024

theorem surrogateDiagonalTailChunk000Sub001Block052Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block052Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block052Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block052Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block052Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block052Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block052Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block052HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block052Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block052Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block052Part000
    + surrogateDiagTailX0RatChunk000Sub001Block052Part001
    + surrogateDiagTailX0RatChunk000Sub001Block052Part002
    + surrogateDiagTailX0RatChunk000Sub001Block052Part003
    + surrogateDiagTailX0RatChunk000Sub001Block052Part004
    + surrogateDiagTailX0RatChunk000Sub001Block052Part005
    + surrogateDiagTailX0RatChunk000Sub001Block052Part006
    + surrogateDiagTailX0RatChunk000Sub001Block052Part007
    + surrogateDiagTailX0RatChunk000Sub001Block052Part008
    + surrogateDiagTailX0RatChunk000Sub001Block052Part009

def surrogateDiagonalTailChunk000Sub001Block052MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block052Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block052Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block052Part010
    + surrogateDiagTailX0RatChunk000Sub001Block052Part011
    + surrogateDiagTailX0RatChunk000Sub001Block052Part012
    + surrogateDiagTailX0RatChunk000Sub001Block052Part013
    + surrogateDiagTailX0RatChunk000Sub001Block052Part014
    + surrogateDiagTailX0RatChunk000Sub001Block052Part015
    + surrogateDiagTailX0RatChunk000Sub001Block052Part016
    + surrogateDiagTailX0RatChunk000Sub001Block052Part017
    + surrogateDiagTailX0RatChunk000Sub001Block052Part018
    + surrogateDiagTailX0RatChunk000Sub001Block052Part019

def surrogateDiagonalTailChunk000Sub001Block052TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block052Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block052Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block052Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block052Part020
    + surrogateDiagTailX0RatChunk000Sub001Block052Part021
    + surrogateDiagTailX0RatChunk000Sub001Block052Part022
    + surrogateDiagTailX0RatChunk000Sub001Block052Part023
    + surrogateDiagTailX0RatChunk000Sub001Block052Part024

def surrogateDiagonalTailChunk000Sub001Block052Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block052HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block052MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block052TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block052 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block052Part000
    + surrogateDiagTailX0RatChunk000Sub001Block052Part001
    + surrogateDiagTailX0RatChunk000Sub001Block052Part002
    + surrogateDiagTailX0RatChunk000Sub001Block052Part003
    + surrogateDiagTailX0RatChunk000Sub001Block052Part004
    + surrogateDiagTailX0RatChunk000Sub001Block052Part005
    + surrogateDiagTailX0RatChunk000Sub001Block052Part006
    + surrogateDiagTailX0RatChunk000Sub001Block052Part007
    + surrogateDiagTailX0RatChunk000Sub001Block052Part008
    + surrogateDiagTailX0RatChunk000Sub001Block052Part009
    + surrogateDiagTailX0RatChunk000Sub001Block052Part010
    + surrogateDiagTailX0RatChunk000Sub001Block052Part011
    + surrogateDiagTailX0RatChunk000Sub001Block052Part012
    + surrogateDiagTailX0RatChunk000Sub001Block052Part013
    + surrogateDiagTailX0RatChunk000Sub001Block052Part014
    + surrogateDiagTailX0RatChunk000Sub001Block052Part015
    + surrogateDiagTailX0RatChunk000Sub001Block052Part016
    + surrogateDiagTailX0RatChunk000Sub001Block052Part017
    + surrogateDiagTailX0RatChunk000Sub001Block052Part018
    + surrogateDiagTailX0RatChunk000Sub001Block052Part019
    + surrogateDiagTailX0RatChunk000Sub001Block052Part020
    + surrogateDiagTailX0RatChunk000Sub001Block052Part021
    + surrogateDiagTailX0RatChunk000Sub001Block052Part022
    + surrogateDiagTailX0RatChunk000Sub001Block052Part023
    + surrogateDiagTailX0RatChunk000Sub001Block052Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block052_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block052Head + surrogateDiagTailX0RatChunk000Sub001Block052Mid + surrogateDiagTailX0RatChunk000Sub001Block052Tail =
      surrogateDiagTailX0RatChunk000Sub001Block052 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block052Head surrogateDiagTailX0RatChunk000Sub001Block052Mid surrogateDiagTailX0RatChunk000Sub001Block052Tail surrogateDiagTailX0RatChunk000Sub001Block052
  ring

def SurrogateDiagonalTailChunk000Sub001Block052HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block052HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block052Head

def SurrogateDiagonalTailChunk000Sub001Block052MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block052MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block052Mid

def SurrogateDiagonalTailChunk000Sub001Block052TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block052TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block052Tail

theorem surrogateDiagonalTailChunk000Sub001Block052_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block052HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block052MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block052TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block052Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block052 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block052HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block052MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block052TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block052Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block052_eq_head_add_mid_add_tail

/-- Block 053 covers tail-support indices [6325,6350) and q from 10451 to 10493. -/

def TailChunk000Sub001Block053Part000SupportExplicit : Finset ℕ :=
  ([10451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part000 : ℚ :=
  (301596526475 : ℚ) / 892143360770835456

def SurrogateDiagonalTailChunk000Sub001Block053Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10451
    = surrogateDiagTailX0RatChunk000Sub001Block053Part000

theorem surrogateDiagonalTailChunk000Sub001Block053Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part000] using hcert

def TailChunk000Sub001Block053Part001SupportExplicit : Finset ℕ :=
  ([10453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part001 : ℚ :=
  (1707268890625 : ℚ) / 7460440512522315552

def SurrogateDiagonalTailChunk000Sub001Block053Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10453
    = surrogateDiagTailX0RatChunk000Sub001Block053Part001

theorem surrogateDiagonalTailChunk000Sub001Block053Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part001] using hcert

def TailChunk000Sub001Block053Part002SupportExplicit : Finset ℕ :=
  ([10454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part002 : ℚ :=
  (426898890625 : ℚ) / 466277532032644722

def SurrogateDiagonalTailChunk000Sub001Block053Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10454
    = surrogateDiagTailX0RatChunk000Sub001Block053Part002

theorem surrogateDiagonalTailChunk000Sub001Block053Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part002] using hcert

def TailChunk000Sub001Block053Part003SupportExplicit : Finset ℕ :=
  ([10455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part003 : ℚ :=
  (998247179 : ℚ) / 859165257891840

def SurrogateDiagonalTailChunk000Sub001Block053Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10455
    = surrogateDiagTailX0RatChunk000Sub001Block053Part003

theorem surrogateDiagonalTailChunk000Sub001Block053Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part003] using hcert

def TailChunk000Sub001Block053Part004SupportExplicit : Finset ℕ :=
  ([10457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part004 : ℚ :=
  (1708575765625 : ℚ) / 7471867568461312512

def SurrogateDiagonalTailChunk000Sub001Block053Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10457
    = surrogateDiagTailX0RatChunk000Sub001Block053Part004

theorem surrogateDiagonalTailChunk000Sub001Block053Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part004] using hcert

def TailChunk000Sub001Block053Part005SupportExplicit : Finset ℕ :=
  ([10459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part005 : ℚ :=
  (1709229390625 : ℚ) / 7477586016544486962

def SurrogateDiagonalTailChunk000Sub001Block053Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10459
    = surrogateDiagTailX0RatChunk000Sub001Block053Part005

theorem surrogateDiagonalTailChunk000Sub001Block053Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part005] using hcert

def TailChunk000Sub001Block053Part006SupportExplicit : Finset ℕ :=
  ([10461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part006 : ℚ :=
  (1075960933 : ℚ) / 1595714396823552

def SurrogateDiagonalTailChunk000Sub001Block053Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10461
    = surrogateDiagTailX0RatChunk000Sub001Block053Part006

theorem surrogateDiagonalTailChunk000Sub001Block053Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part006] using hcert

def TailChunk000Sub001Block053Part007SupportExplicit : Finset ℕ :=
  ([10462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part007 : ℚ :=
  (684084025 : ℚ) / 748330774637682

def SurrogateDiagonalTailChunk000Sub001Block053Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10462
    = surrogateDiagTailX0RatChunk000Sub001Block053Part007

theorem surrogateDiagonalTailChunk000Sub001Block053Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part007] using hcert

def TailChunk000Sub001Block053Part008SupportExplicit : Finset ℕ :=
  ([10463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part008 : ℚ :=
  (1710537015625 : ℚ) / 7489032759213642642

def SurrogateDiagonalTailChunk000Sub001Block053Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10463
    = surrogateDiagTailX0RatChunk000Sub001Block053Part008

theorem surrogateDiagonalTailChunk000Sub001Block053Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part008] using hcert

def TailChunk000Sub001Block053Part009SupportExplicit : Finset ℕ :=
  ([10465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part009 : ℚ :=
  (146713214575 : ℚ) / 183174431521112064

def SurrogateDiagonalTailChunk000Sub001Block053Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10465
    = surrogateDiagTailX0RatChunk000Sub001Block053Part009

theorem surrogateDiagonalTailChunk000Sub001Block053Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part009] using hcert

def TailChunk000Sub001Block053Part010SupportExplicit : Finset ℕ :=
  ([10466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part010 : ℚ :=
  (427879515625 : ℚ) / 468422566019407872

def SurrogateDiagonalTailChunk000Sub001Block053Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10466
    = surrogateDiagTailX0RatChunk000Sub001Block053Part010

theorem surrogateDiagonalTailChunk000Sub001Block053Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part010] using hcert

def TailChunk000Sub001Block053Part011SupportExplicit : Finset ℕ :=
  ([10470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part011 : ℚ :=
  (301127630575 : ℚ) / 50070569136685056

def SurrogateDiagonalTailChunk000Sub001Block053Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10470
    = surrogateDiagTailX0RatChunk000Sub001Block053Part011

theorem surrogateDiagonalTailChunk000Sub001Block053Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part011] using hcert

def TailChunk000Sub001Block053Part012SupportExplicit : Finset ℕ :=
  ([10471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part012 : ℚ :=
  (3269020261475 : ℚ) / 13280159758495048704

def SurrogateDiagonalTailChunk000Sub001Block053Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10471
    = surrogateDiagTailX0RatChunk000Sub001Block053Part012

theorem surrogateDiagonalTailChunk000Sub001Block053Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part012] using hcert

def TailChunk000Sub001Block053Part013SupportExplicit : Finset ℕ :=
  ([10473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part013 : ℚ :=
  (121825986037 : ℚ) / 237415211163523200

def SurrogateDiagonalTailChunk000Sub001Block053Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10473
    = surrogateDiagTailX0RatChunk000Sub001Block053Part013

theorem surrogateDiagonalTailChunk000Sub001Block053Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part013] using hcert

def TailChunk000Sub001Block053Part014SupportExplicit : Finset ℕ :=
  ([10474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part014 : ℚ :=
  (428533890625 : ℚ) / 469856694526155552

def SurrogateDiagonalTailChunk000Sub001Block053Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10474
    = surrogateDiagTailX0RatChunk000Sub001Block053Part014

theorem surrogateDiagonalTailChunk000Sub001Block053Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part014] using hcert

def TailChunk000Sub001Block053Part015SupportExplicit : Finset ℕ :=
  ([10477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part015 : ℚ :=
  (1715117640625 : ℚ) / 7529199878695325472

def SurrogateDiagonalTailChunk000Sub001Block053Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10477
    = surrogateDiagTailX0RatChunk000Sub001Block053Part015

theorem surrogateDiagonalTailChunk000Sub001Block053Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part015] using hcert

def TailChunk000Sub001Block053Part016SupportExplicit : Finset ℕ :=
  ([10479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part016 : ℚ :=
  (274230225325 : ℚ) / 354345322825746432

def SurrogateDiagonalTailChunk000Sub001Block053Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10479
    = surrogateDiagTailX0RatChunk000Sub001Block053Part016

theorem surrogateDiagonalTailChunk000Sub001Block053Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part016] using hcert

def TailChunk000Sub001Block053Part017SupportExplicit : Finset ℕ :=
  ([10481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part017 : ℚ :=
  (6597613301575 : ℚ) / 27193811537480381568

def SurrogateDiagonalTailChunk000Sub001Block053Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10481
    = surrogateDiagTailX0RatChunk000Sub001Block053Part017

theorem surrogateDiagonalTailChunk000Sub001Block053Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part017] using hcert

def TailChunk000Sub001Block053Part018SupportExplicit : Finset ℕ :=
  ([10482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part018 : ℚ :=
  (38127275 : ℚ) / 12391266403008

def SurrogateDiagonalTailChunk000Sub001Block053Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10482
    = surrogateDiagTailX0RatChunk000Sub001Block053Part018

theorem surrogateDiagonalTailChunk000Sub001Block053Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part018] using hcert

def TailChunk000Sub001Block053Part019SupportExplicit : Finset ℕ :=
  ([10483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part019 : ℚ :=
  (235794722881 : ℚ) / 821551217804083200

def SurrogateDiagonalTailChunk000Sub001Block053Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10483
    = surrogateDiagTailX0RatChunk000Sub001Block053Part019

theorem surrogateDiagonalTailChunk000Sub001Block053Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part019] using hcert

def TailChunk000Sub001Block053Part020SupportExplicit : Finset ℕ :=
  ([10487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part020 : ℚ :=
  (1718393265625 : ℚ) / 7557989444873858802

def SurrogateDiagonalTailChunk000Sub001Block053Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10487
    = surrogateDiagTailX0RatChunk000Sub001Block053Part020

theorem surrogateDiagonalTailChunk000Sub001Block053Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part020] using hcert

def TailChunk000Sub001Block053Part021SupportExplicit : Finset ℕ :=
  ([10489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part021 : ℚ :=
  (148646484375 : ℚ) / 561798205663084544

def SurrogateDiagonalTailChunk000Sub001Block053Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10489
    = surrogateDiagTailX0RatChunk000Sub001Block053Part021

theorem surrogateDiagonalTailChunk000Sub001Block053Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part021] using hcert

def TailChunk000Sub001Block053Part022SupportExplicit : Finset ℕ :=
  ([10490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part022 : ℚ :=
  (687202287875 : ℚ) / 386084137840410624

def SurrogateDiagonalTailChunk000Sub001Block053Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10490
    = surrogateDiagTailX0RatChunk000Sub001Block053Part022

theorem surrogateDiagonalTailChunk000Sub001Block053Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part022] using hcert

def TailChunk000Sub001Block053Part023SupportExplicit : Finset ℕ :=
  ([10491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part023 : ℚ :=
  (422959648475 : ℚ) / 534959636204814336

def SurrogateDiagonalTailChunk000Sub001Block053Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10491
    = surrogateDiagTailX0RatChunk000Sub001Block053Part023

theorem surrogateDiagonalTailChunk000Sub001Block053Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part023] using hcert

def TailChunk000Sub001Block053Part024SupportExplicit : Finset ℕ :=
  ([10493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block053Part024 : ℚ :=
  (11901781225 : ℚ) / 36425129114939166

def SurrogateDiagonalTailChunk000Sub001Block053Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10493
    = surrogateDiagTailX0RatChunk000Sub001Block053Part024

theorem surrogateDiagonalTailChunk000Sub001Block053Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block053Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block053Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block053Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block053Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block053Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block053Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block053HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block053Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block053Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block053Part000
    + surrogateDiagTailX0RatChunk000Sub001Block053Part001
    + surrogateDiagTailX0RatChunk000Sub001Block053Part002
    + surrogateDiagTailX0RatChunk000Sub001Block053Part003
    + surrogateDiagTailX0RatChunk000Sub001Block053Part004
    + surrogateDiagTailX0RatChunk000Sub001Block053Part005
    + surrogateDiagTailX0RatChunk000Sub001Block053Part006
    + surrogateDiagTailX0RatChunk000Sub001Block053Part007
    + surrogateDiagTailX0RatChunk000Sub001Block053Part008
    + surrogateDiagTailX0RatChunk000Sub001Block053Part009

def surrogateDiagonalTailChunk000Sub001Block053MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block053Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block053Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block053Part010
    + surrogateDiagTailX0RatChunk000Sub001Block053Part011
    + surrogateDiagTailX0RatChunk000Sub001Block053Part012
    + surrogateDiagTailX0RatChunk000Sub001Block053Part013
    + surrogateDiagTailX0RatChunk000Sub001Block053Part014
    + surrogateDiagTailX0RatChunk000Sub001Block053Part015
    + surrogateDiagTailX0RatChunk000Sub001Block053Part016
    + surrogateDiagTailX0RatChunk000Sub001Block053Part017
    + surrogateDiagTailX0RatChunk000Sub001Block053Part018
    + surrogateDiagTailX0RatChunk000Sub001Block053Part019

def surrogateDiagonalTailChunk000Sub001Block053TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block053Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block053Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block053Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block053Part020
    + surrogateDiagTailX0RatChunk000Sub001Block053Part021
    + surrogateDiagTailX0RatChunk000Sub001Block053Part022
    + surrogateDiagTailX0RatChunk000Sub001Block053Part023
    + surrogateDiagTailX0RatChunk000Sub001Block053Part024

def surrogateDiagonalTailChunk000Sub001Block053Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block053HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block053MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block053TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block053 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block053Part000
    + surrogateDiagTailX0RatChunk000Sub001Block053Part001
    + surrogateDiagTailX0RatChunk000Sub001Block053Part002
    + surrogateDiagTailX0RatChunk000Sub001Block053Part003
    + surrogateDiagTailX0RatChunk000Sub001Block053Part004
    + surrogateDiagTailX0RatChunk000Sub001Block053Part005
    + surrogateDiagTailX0RatChunk000Sub001Block053Part006
    + surrogateDiagTailX0RatChunk000Sub001Block053Part007
    + surrogateDiagTailX0RatChunk000Sub001Block053Part008
    + surrogateDiagTailX0RatChunk000Sub001Block053Part009
    + surrogateDiagTailX0RatChunk000Sub001Block053Part010
    + surrogateDiagTailX0RatChunk000Sub001Block053Part011
    + surrogateDiagTailX0RatChunk000Sub001Block053Part012
    + surrogateDiagTailX0RatChunk000Sub001Block053Part013
    + surrogateDiagTailX0RatChunk000Sub001Block053Part014
    + surrogateDiagTailX0RatChunk000Sub001Block053Part015
    + surrogateDiagTailX0RatChunk000Sub001Block053Part016
    + surrogateDiagTailX0RatChunk000Sub001Block053Part017
    + surrogateDiagTailX0RatChunk000Sub001Block053Part018
    + surrogateDiagTailX0RatChunk000Sub001Block053Part019
    + surrogateDiagTailX0RatChunk000Sub001Block053Part020
    + surrogateDiagTailX0RatChunk000Sub001Block053Part021
    + surrogateDiagTailX0RatChunk000Sub001Block053Part022
    + surrogateDiagTailX0RatChunk000Sub001Block053Part023
    + surrogateDiagTailX0RatChunk000Sub001Block053Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block053_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block053Head + surrogateDiagTailX0RatChunk000Sub001Block053Mid + surrogateDiagTailX0RatChunk000Sub001Block053Tail =
      surrogateDiagTailX0RatChunk000Sub001Block053 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block053Head surrogateDiagTailX0RatChunk000Sub001Block053Mid surrogateDiagTailX0RatChunk000Sub001Block053Tail surrogateDiagTailX0RatChunk000Sub001Block053
  ring

def SurrogateDiagonalTailChunk000Sub001Block053HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block053HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block053Head

def SurrogateDiagonalTailChunk000Sub001Block053MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block053MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block053Mid

def SurrogateDiagonalTailChunk000Sub001Block053TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block053TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block053Tail

theorem surrogateDiagonalTailChunk000Sub001Block053_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block053HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block053MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block053TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block053Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block053 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block053HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block053MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block053TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block053Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block053_eq_head_add_mid_add_tail

/-- Block 054 covers tail-support indices [6350,6375) and q from 10495 to 10534. -/

def TailChunk000Sub001Block054Part000SupportExplicit : Finset ℕ :=
  ([10495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part000 : ℚ :=
  (4678394755225 : ℚ) / 12401915261677160448

def SurrogateDiagonalTailChunk000Sub001Block054Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10495
    = surrogateDiagTailX0RatChunk000Sub001Block054Part000

theorem surrogateDiagonalTailChunk000Sub001Block054Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part000] using hcert

def TailChunk000Sub001Block054Part001SupportExplicit : Finset ℕ :=
  ([10497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part001 : ℚ :=
  (478123487525 : ℚ) / 748748689233968016

def SurrogateDiagonalTailChunk000Sub001Block054Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10497
    = surrogateDiagTailX0RatChunk000Sub001Block054Part001

theorem surrogateDiagonalTailChunk000Sub001Block054Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part001] using hcert

def TailChunk000Sub001Block054Part002SupportExplicit : Finset ℕ :=
  ([10498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part002 : ℚ :=
  (13210270763 : ℚ) / 12907406616330240

def SurrogateDiagonalTailChunk000Sub001Block054Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10498
    = surrogateDiagTailX0RatChunk000Sub001Block054Part002

theorem surrogateDiagonalTailChunk000Sub001Block054Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part002] using hcert

def TailChunk000Sub001Block054Part003SupportExplicit : Finset ℕ :=
  ([10499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part003 : ℚ :=
  (1722328140625 : ℚ) / 7592645816558218002

def SurrogateDiagonalTailChunk000Sub001Block054Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10499
    = surrogateDiagTailX0RatChunk000Sub001Block054Part003

theorem surrogateDiagonalTailChunk000Sub001Block054Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part003] using hcert

def TailChunk000Sub001Block054Part004SupportExplicit : Finset ℕ :=
  ([10501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part004 : ℚ :=
  (110271001 : ℚ) / 486299740500000

def SurrogateDiagonalTailChunk000Sub001Block054Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10501
    = surrogateDiagTailX0RatChunk000Sub001Block054Part004

theorem surrogateDiagonalTailChunk000Sub001Block054Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part004] using hcert

def TailChunk000Sub001Block054Part005SupportExplicit : Finset ℕ :=
  ([10502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part005 : ℚ :=
  (836789531375 : ℚ) / 848475929085886464

def SurrogateDiagonalTailChunk000Sub001Block054Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10502
    = surrogateDiagTailX0RatChunk000Sub001Block054Part005

theorem surrogateDiagonalTailChunk000Sub001Block054Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part005] using hcert

def TailChunk000Sub001Block054Part006SupportExplicit : Finset ℕ :=
  ([10505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part006 : ℚ :=
  (85230476501 : ℚ) / 166844242176000000

def SurrogateDiagonalTailChunk000Sub001Block054Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10505
    = surrogateDiagTailX0RatChunk000Sub001Block054Part006

theorem surrogateDiagonalTailChunk000Sub001Block054Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part006] using hcert

def TailChunk000Sub001Block054Part007SupportExplicit : Finset ℕ :=
  ([10506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part007 : ℚ :=
  (35573375 : ℚ) / 9458436538368

def SurrogateDiagonalTailChunk000Sub001Block054Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10506
    = surrogateDiagTailX0RatChunk000Sub001Block054Part007

theorem surrogateDiagonalTailChunk000Sub001Block054Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part007] using hcert

def TailChunk000Sub001Block054Part008SupportExplicit : Finset ℕ :=
  ([10507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part008 : ℚ :=
  (2421982940075 : ℚ) / 6296080844598764544

def SurrogateDiagonalTailChunk000Sub001Block054Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10507
    = surrogateDiagTailX0RatChunk000Sub001Block054Part008

theorem surrogateDiagonalTailChunk000Sub001Block054Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part008] using hcert

def TailChunk000Sub001Block054Part009SupportExplicit : Finset ℕ :=
  ([10509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part009 : ℚ :=
  (5781918505 : ℚ) / 8158755787112448

def SurrogateDiagonalTailChunk000Sub001Block054Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10509
    = surrogateDiagTailX0RatChunk000Sub001Block054Part009

theorem surrogateDiagonalTailChunk000Sub001Block054Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part009] using hcert

def TailChunk000Sub001Block054Part010SupportExplicit : Finset ℕ :=
  ([10510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part010 : ℚ :=
  (5518602499 : ℚ) / 3112318339200000

def SurrogateDiagonalTailChunk000Sub001Block054Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10510
    = surrogateDiagTailX0RatChunk000Sub001Block054Part010

theorem surrogateDiagonalTailChunk000Sub001Block054Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part010] using hcert

def TailChunk000Sub001Block054Part011SupportExplicit : Finset ℕ :=
  ([10511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part011 : ℚ :=
  (6427764445825 : ℚ) / 25326603587277324288

def SurrogateDiagonalTailChunk000Sub001Block054Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10511
    = surrogateDiagTailX0RatChunk000Sub001Block054Part011

theorem surrogateDiagonalTailChunk000Sub001Block054Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part011] using hcert

def TailChunk000Sub001Block054Part012SupportExplicit : Finset ℕ :=
  ([10513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part012 : ℚ :=
  (1726924515625 : ℚ) / 7633228733351534592

def SurrogateDiagonalTailChunk000Sub001Block054Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10513
    = surrogateDiagTailX0RatChunk000Sub001Block054Part012

theorem surrogateDiagonalTailChunk000Sub001Block054Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part012] using hcert

def TailChunk000Sub001Block054Part013SupportExplicit : Finset ℕ :=
  ([10514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part013 : ℚ :=
  (219071111 : ℚ) / 151905375000000

def SurrogateDiagonalTailChunk000Sub001Block054Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10514
    = surrogateDiagTailX0RatChunk000Sub001Block054Part013

theorem surrogateDiagonalTailChunk000Sub001Block054Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part013] using hcert

def TailChunk000Sub001Block054Part014SupportExplicit : Finset ℕ :=
  ([10515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part014 : ℚ :=
  (111594860071 : ℚ) / 98364628992000000

def SurrogateDiagonalTailChunk000Sub001Block054Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10515
    = surrogateDiagTailX0RatChunk000Sub001Block054Part014

theorem surrogateDiagonalTailChunk000Sub001Block054Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part014] using hcert

def TailChunk000Sub001Block054Part015SupportExplicit : Finset ℕ :=
  ([10517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part015 : ℚ :=
  (6084356592025 : ℚ) / 22100255072573718528

def SurrogateDiagonalTailChunk000Sub001Block054Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10517
    = surrogateDiagTailX0RatChunk000Sub001Block054Part015

theorem surrogateDiagonalTailChunk000Sub001Block054Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part015] using hcert

def TailChunk000Sub001Block054Part016SupportExplicit : Finset ℕ :=
  ([10518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part016 : ℚ :=
  (38389625 : ℚ) / 12562473074688

def SurrogateDiagonalTailChunk000Sub001Block054Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10518
    = surrogateDiagTailX0RatChunk000Sub001Block054Part016

theorem surrogateDiagonalTailChunk000Sub001Block054Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part016] using hcert

def TailChunk000Sub001Block054Part017SupportExplicit : Finset ℕ :=
  ([10519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part017 : ℚ :=
  (6694043905375 : ℚ) / 28099655432333641728

def SurrogateDiagonalTailChunk000Sub001Block054Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10519
    = surrogateDiagTailX0RatChunk000Sub001Block054Part017

theorem surrogateDiagonalTailChunk000Sub001Block054Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part017] using hcert

def TailChunk000Sub001Block054Part018SupportExplicit : Finset ℕ :=
  ([10522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block054Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10522
    = surrogateDiagTailX0RatChunk000Sub001Block054Part018

theorem surrogateDiagonalTailChunk000Sub001Block054Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part018] using hcert

def TailChunk000Sub001Block054Part019SupportExplicit : Finset ℕ :=
  ([10523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part019 : ℚ :=
  (195692721925 : ℚ) / 23903455635759955968

def SurrogateDiagonalTailChunk000Sub001Block054Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10523
    = surrogateDiagTailX0RatChunk000Sub001Block054Part019

theorem surrogateDiagonalTailChunk000Sub001Block054Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part019] using hcert

def TailChunk000Sub001Block054Part020SupportExplicit : Finset ℕ :=
  ([10526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part020 : ℚ :=
  (22756689925 : ℚ) / 380796735173571072

def SurrogateDiagonalTailChunk000Sub001Block054Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10526
    = surrogateDiagTailX0RatChunk000Sub001Block054Part020

theorem surrogateDiagonalTailChunk000Sub001Block054Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part020] using hcert

def TailChunk000Sub001Block054Part021SupportExplicit : Finset ℕ :=
  ([10529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block054Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10529
    = surrogateDiagTailX0RatChunk000Sub001Block054Part021

theorem surrogateDiagonalTailChunk000Sub001Block054Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part021] using hcert

def TailChunk000Sub001Block054Part022SupportExplicit : Finset ℕ :=
  ([10531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block054Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10531
    = surrogateDiagTailX0RatChunk000Sub001Block054Part022

theorem surrogateDiagonalTailChunk000Sub001Block054Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part022] using hcert

def TailChunk000Sub001Block054Part023SupportExplicit : Finset ℕ :=
  ([10533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part023 : ℚ :=
  (3082525399 : ℚ) / 24290435357248320

def SurrogateDiagonalTailChunk000Sub001Block054Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10533
    = surrogateDiagTailX0RatChunk000Sub001Block054Part023

theorem surrogateDiagonalTailChunk000Sub001Block054Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part023] using hcert

def TailChunk000Sub001Block054Part024SupportExplicit : Finset ℕ :=
  ([10534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block054Part024 : ℚ :=
  (1647905488825 : ℚ) / 1582912724204832768

def SurrogateDiagonalTailChunk000Sub001Block054Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10534
    = surrogateDiagTailX0RatChunk000Sub001Block054Part024

theorem surrogateDiagonalTailChunk000Sub001Block054Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block054Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block054Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block054Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block054Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block054Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block054Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block054HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block054Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block054Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block054Part000
    + surrogateDiagTailX0RatChunk000Sub001Block054Part001
    + surrogateDiagTailX0RatChunk000Sub001Block054Part002
    + surrogateDiagTailX0RatChunk000Sub001Block054Part003
    + surrogateDiagTailX0RatChunk000Sub001Block054Part004
    + surrogateDiagTailX0RatChunk000Sub001Block054Part005
    + surrogateDiagTailX0RatChunk000Sub001Block054Part006
    + surrogateDiagTailX0RatChunk000Sub001Block054Part007
    + surrogateDiagTailX0RatChunk000Sub001Block054Part008
    + surrogateDiagTailX0RatChunk000Sub001Block054Part009

def surrogateDiagonalTailChunk000Sub001Block054MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block054Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block054Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block054Part010
    + surrogateDiagTailX0RatChunk000Sub001Block054Part011
    + surrogateDiagTailX0RatChunk000Sub001Block054Part012
    + surrogateDiagTailX0RatChunk000Sub001Block054Part013
    + surrogateDiagTailX0RatChunk000Sub001Block054Part014
    + surrogateDiagTailX0RatChunk000Sub001Block054Part015
    + surrogateDiagTailX0RatChunk000Sub001Block054Part016
    + surrogateDiagTailX0RatChunk000Sub001Block054Part017
    + surrogateDiagTailX0RatChunk000Sub001Block054Part018
    + surrogateDiagTailX0RatChunk000Sub001Block054Part019

def surrogateDiagonalTailChunk000Sub001Block054TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block054Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block054Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block054Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block054Part020
    + surrogateDiagTailX0RatChunk000Sub001Block054Part021
    + surrogateDiagTailX0RatChunk000Sub001Block054Part022
    + surrogateDiagTailX0RatChunk000Sub001Block054Part023
    + surrogateDiagTailX0RatChunk000Sub001Block054Part024

def surrogateDiagonalTailChunk000Sub001Block054Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block054HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block054MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block054TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block054 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block054Part000
    + surrogateDiagTailX0RatChunk000Sub001Block054Part001
    + surrogateDiagTailX0RatChunk000Sub001Block054Part002
    + surrogateDiagTailX0RatChunk000Sub001Block054Part003
    + surrogateDiagTailX0RatChunk000Sub001Block054Part004
    + surrogateDiagTailX0RatChunk000Sub001Block054Part005
    + surrogateDiagTailX0RatChunk000Sub001Block054Part006
    + surrogateDiagTailX0RatChunk000Sub001Block054Part007
    + surrogateDiagTailX0RatChunk000Sub001Block054Part008
    + surrogateDiagTailX0RatChunk000Sub001Block054Part009
    + surrogateDiagTailX0RatChunk000Sub001Block054Part010
    + surrogateDiagTailX0RatChunk000Sub001Block054Part011
    + surrogateDiagTailX0RatChunk000Sub001Block054Part012
    + surrogateDiagTailX0RatChunk000Sub001Block054Part013
    + surrogateDiagTailX0RatChunk000Sub001Block054Part014
    + surrogateDiagTailX0RatChunk000Sub001Block054Part015
    + surrogateDiagTailX0RatChunk000Sub001Block054Part016
    + surrogateDiagTailX0RatChunk000Sub001Block054Part017
    + surrogateDiagTailX0RatChunk000Sub001Block054Part018
    + surrogateDiagTailX0RatChunk000Sub001Block054Part019
    + surrogateDiagTailX0RatChunk000Sub001Block054Part020
    + surrogateDiagTailX0RatChunk000Sub001Block054Part021
    + surrogateDiagTailX0RatChunk000Sub001Block054Part022
    + surrogateDiagTailX0RatChunk000Sub001Block054Part023
    + surrogateDiagTailX0RatChunk000Sub001Block054Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block054_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block054Head + surrogateDiagTailX0RatChunk000Sub001Block054Mid + surrogateDiagTailX0RatChunk000Sub001Block054Tail =
      surrogateDiagTailX0RatChunk000Sub001Block054 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block054Head surrogateDiagTailX0RatChunk000Sub001Block054Mid surrogateDiagTailX0RatChunk000Sub001Block054Tail surrogateDiagTailX0RatChunk000Sub001Block054
  ring

def SurrogateDiagonalTailChunk000Sub001Block054HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block054HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block054Head

def SurrogateDiagonalTailChunk000Sub001Block054MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block054MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block054Mid

def SurrogateDiagonalTailChunk000Sub001Block054TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block054TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block054Tail

theorem surrogateDiagonalTailChunk000Sub001Block054_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block054HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block054MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block054TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block054Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block054 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block054HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block054MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block054TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block054Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block054_eq_head_add_mid_add_tail

/-- Block 055 covers tail-support indices [6375,6400) and q from 10537 to 10577. -/

def TailChunk000Sub001Block055Part000SupportExplicit : Finset ℕ :=
  ([10537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part000 : ℚ :=
  (600317649 : ℚ) / 183288588350259200

def SurrogateDiagonalTailChunk000Sub001Block055Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10537
    = surrogateDiagTailX0RatChunk000Sub001Block055Part000

theorem surrogateDiagonalTailChunk000Sub001Block055Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part000] using hcert

def TailChunk000Sub001Block055Part001SupportExplicit : Finset ℕ :=
  ([10538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part001 : ℚ :=
  (3148526579 : ℚ) / 2610768962182560

def SurrogateDiagonalTailChunk000Sub001Block055Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10538
    = surrogateDiagTailX0RatChunk000Sub001Block055Part001

theorem surrogateDiagonalTailChunk000Sub001Block055Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part001] using hcert

def TailChunk000Sub001Block055Part002SupportExplicit : Finset ℕ :=
  ([10541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part002 : ℚ :=
  (7103101225 : ℚ) / 3166080401698607232

def SurrogateDiagonalTailChunk000Sub001Block055Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10541
    = surrogateDiagTailX0RatChunk000Sub001Block055Part002

theorem surrogateDiagonalTailChunk000Sub001Block055Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part002] using hcert

def TailChunk000Sub001Block055Part003SupportExplicit : Finset ℕ :=
  ([10542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part003 : ℚ :=
  (38750804617 : ℚ) / 8101620000000000

def SurrogateDiagonalTailChunk000Sub001Block055Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10542
    = surrogateDiagTailX0RatChunk000Sub001Block055Part003

theorem surrogateDiagonalTailChunk000Sub001Block055Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part003] using hcert

def TailChunk000Sub001Block055Part004SupportExplicit : Finset ℕ :=
  ([10543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part004 : ℚ :=
  (399270595 : ℚ) / 35711813200693248

def SurrogateDiagonalTailChunk000Sub001Block055Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10543
    = surrogateDiagTailX0RatChunk000Sub001Block055Part004

theorem surrogateDiagonalTailChunk000Sub001Block055Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part004] using hcert

def TailChunk000Sub001Block055Part005SupportExplicit : Finset ℕ :=
  ([10545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part005 : ℚ :=
  (863820957175 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub001Block055Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10545
    = surrogateDiagTailX0RatChunk000Sub001Block055Part005

theorem surrogateDiagonalTailChunk000Sub001Block055Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part005] using hcert

def TailChunk000Sub001Block055Part006SupportExplicit : Finset ℕ :=
  ([10546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part006 : ℚ :=
  (434445765625 : ℚ) / 482912529813484032

def SurrogateDiagonalTailChunk000Sub001Block055Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10546
    = surrogateDiagTailX0RatChunk000Sub001Block055Part006

theorem surrogateDiagonalTailChunk000Sub001Block055Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part006] using hcert

def TailChunk000Sub001Block055Part007SupportExplicit : Finset ℕ :=
  ([10547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part007 : ℚ :=
  (38659104875 : ℚ) / 14049827716166820864

def SurrogateDiagonalTailChunk000Sub001Block055Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10547
    = surrogateDiagTailX0RatChunk000Sub001Block055Part007

theorem surrogateDiagonalTailChunk000Sub001Block055Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part007] using hcert

def TailChunk000Sub001Block055Part008SupportExplicit : Finset ℕ :=
  ([10549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part008 : ℚ :=
  (1602902977 : ℚ) / 24636271421030400

def SurrogateDiagonalTailChunk000Sub001Block055Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10549
    = surrogateDiagTailX0RatChunk000Sub001Block055Part008

theorem surrogateDiagonalTailChunk000Sub001Block055Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part008] using hcert

def TailChunk000Sub001Block055Part009SupportExplicit : Finset ℕ :=
  ([10551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part009 : ℚ :=
  (48329131225 : ℚ) / 382139846210544768

def SurrogateDiagonalTailChunk000Sub001Block055Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10551
    = surrogateDiagTailX0RatChunk000Sub001Block055Part009

theorem surrogateDiagonalTailChunk000Sub001Block055Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part009] using hcert

def TailChunk000Sub001Block055Part010SupportExplicit : Finset ℕ :=
  ([10553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part010 : ℚ :=
  (2883053851 : ℚ) / 1134502975800115200

def SurrogateDiagonalTailChunk000Sub001Block055Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10553
    = surrogateDiagTailX0RatChunk000Sub001Block055Part010

theorem surrogateDiagonalTailChunk000Sub001Block055Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part010] using hcert

def TailChunk000Sub001Block055Part011SupportExplicit : Finset ℕ :=
  ([10554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part011 : ℚ :=
  (38652875 : ℚ) / 12735447784128

def SurrogateDiagonalTailChunk000Sub001Block055Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10554
    = surrogateDiagTailX0RatChunk000Sub001Block055Part011

theorem surrogateDiagonalTailChunk000Sub001Block055Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part011] using hcert

def TailChunk000Sub001Block055Part012SupportExplicit : Finset ℕ :=
  ([10555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part012 : ℚ :=
  (261151499 : ℚ) / 3965031729776400

def SurrogateDiagonalTailChunk000Sub001Block055Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10555
    = surrogateDiagTailX0RatChunk000Sub001Block055Part012

theorem surrogateDiagonalTailChunk000Sub001Block055Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part012] using hcert

def TailChunk000Sub001Block055Part013SupportExplicit : Finset ℕ :=
  ([10558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part013 : ℚ :=
  (435435015625 : ℚ) / 485114673444392082

def SurrogateDiagonalTailChunk000Sub001Block055Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10558
    = surrogateDiagTailX0RatChunk000Sub001Block055Part013

theorem surrogateDiagonalTailChunk000Sub001Block055Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part013] using hcert

def TailChunk000Sub001Block055Part014SupportExplicit : Finset ℕ :=
  ([10559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block055Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10559
    = surrogateDiagTailX0RatChunk000Sub001Block055Part014

theorem surrogateDiagonalTailChunk000Sub001Block055Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part014] using hcert

def TailChunk000Sub001Block055Part015SupportExplicit : Finset ℕ :=
  ([10561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part015 : ℚ :=
  (18330679075 : ℚ) / 7101643237713975072

def SurrogateDiagonalTailChunk000Sub001Block055Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10561
    = surrogateDiagTailX0RatChunk000Sub001Block055Part015

theorem surrogateDiagonalTailChunk000Sub001Block055Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part015] using hcert

def TailChunk000Sub001Block055Part016SupportExplicit : Finset ℕ :=
  ([10562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part016 : ℚ :=
  (697224025 : ℚ) / 777360627597312

def SurrogateDiagonalTailChunk000Sub001Block055Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10562
    = surrogateDiagTailX0RatChunk000Sub001Block055Part016

theorem surrogateDiagonalTailChunk000Sub001Block055Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part016] using hcert

def TailChunk000Sub001Block055Part017SupportExplicit : Finset ℕ :=
  ([10563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part017 : ℚ :=
  (419260773125 : ℚ) / 1646405150321746944

def SurrogateDiagonalTailChunk000Sub001Block055Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10563
    = surrogateDiagTailX0RatChunk000Sub001Block055Part017

theorem surrogateDiagonalTailChunk000Sub001Block055Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part017] using hcert

def TailChunk000Sub001Block055Part018SupportExplicit : Finset ℕ :=
  ([10565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part018 : ℚ :=
  (186235659175 : ℚ) / 4245425507518119936

def SurrogateDiagonalTailChunk000Sub001Block055Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10565
    = surrogateDiagTailX0RatChunk000Sub001Block055Part018

theorem surrogateDiagonalTailChunk000Sub001Block055Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part018] using hcert

def TailChunk000Sub001Block055Part019SupportExplicit : Finset ℕ :=
  ([10567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block055Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10567
    = surrogateDiagTailX0RatChunk000Sub001Block055Part019

theorem surrogateDiagonalTailChunk000Sub001Block055Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part019] using hcert

def TailChunk000Sub001Block055Part020SupportExplicit : Finset ℕ :=
  ([10569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part020 : ℚ :=
  (58970682679 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub001Block055Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10569
    = surrogateDiagTailX0RatChunk000Sub001Block055Part020

theorem surrogateDiagonalTailChunk000Sub001Block055Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part020] using hcert

def TailChunk000Sub001Block055Part021SupportExplicit : Finset ℕ :=
  ([10570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part021 : ℚ :=
  (22315510811 : ℚ) / 8399759616000000

def SurrogateDiagonalTailChunk000Sub001Block055Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10570
    = surrogateDiagTailX0RatChunk000Sub001Block055Part021

theorem surrogateDiagonalTailChunk000Sub001Block055Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part021] using hcert

def TailChunk000Sub001Block055Part022SupportExplicit : Finset ℕ :=
  ([10573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part022 : ℚ :=
  (63485530375 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk000Sub001Block055Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10573
    = surrogateDiagTailX0RatChunk000Sub001Block055Part022

theorem surrogateDiagonalTailChunk000Sub001Block055Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part022] using hcert

def TailChunk000Sub001Block055Part023SupportExplicit : Finset ℕ :=
  ([10574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part023 : ℚ :=
  (32660006051 : ℚ) / 30267988515225600

def SurrogateDiagonalTailChunk000Sub001Block055Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10574
    = surrogateDiagTailX0RatChunk000Sub001Block055Part023

theorem surrogateDiagonalTailChunk000Sub001Block055Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part023] using hcert

def TailChunk000Sub001Block055Part024SupportExplicit : Finset ℕ :=
  ([10577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block055Part024 : ℚ :=
  (22862295853 : ℚ) / 673906493243779200

def SurrogateDiagonalTailChunk000Sub001Block055Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10577
    = surrogateDiagTailX0RatChunk000Sub001Block055Part024

theorem surrogateDiagonalTailChunk000Sub001Block055Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block055Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block055Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block055Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block055Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block055Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block055Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block055HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block055Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block055Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block055Part000
    + surrogateDiagTailX0RatChunk000Sub001Block055Part001
    + surrogateDiagTailX0RatChunk000Sub001Block055Part002
    + surrogateDiagTailX0RatChunk000Sub001Block055Part003
    + surrogateDiagTailX0RatChunk000Sub001Block055Part004
    + surrogateDiagTailX0RatChunk000Sub001Block055Part005
    + surrogateDiagTailX0RatChunk000Sub001Block055Part006
    + surrogateDiagTailX0RatChunk000Sub001Block055Part007
    + surrogateDiagTailX0RatChunk000Sub001Block055Part008
    + surrogateDiagTailX0RatChunk000Sub001Block055Part009

def surrogateDiagonalTailChunk000Sub001Block055MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block055Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block055Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block055Part010
    + surrogateDiagTailX0RatChunk000Sub001Block055Part011
    + surrogateDiagTailX0RatChunk000Sub001Block055Part012
    + surrogateDiagTailX0RatChunk000Sub001Block055Part013
    + surrogateDiagTailX0RatChunk000Sub001Block055Part014
    + surrogateDiagTailX0RatChunk000Sub001Block055Part015
    + surrogateDiagTailX0RatChunk000Sub001Block055Part016
    + surrogateDiagTailX0RatChunk000Sub001Block055Part017
    + surrogateDiagTailX0RatChunk000Sub001Block055Part018
    + surrogateDiagTailX0RatChunk000Sub001Block055Part019

def surrogateDiagonalTailChunk000Sub001Block055TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block055Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block055Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block055Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block055Part020
    + surrogateDiagTailX0RatChunk000Sub001Block055Part021
    + surrogateDiagTailX0RatChunk000Sub001Block055Part022
    + surrogateDiagTailX0RatChunk000Sub001Block055Part023
    + surrogateDiagTailX0RatChunk000Sub001Block055Part024

def surrogateDiagonalTailChunk000Sub001Block055Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block055HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block055MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block055TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block055 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block055Part000
    + surrogateDiagTailX0RatChunk000Sub001Block055Part001
    + surrogateDiagTailX0RatChunk000Sub001Block055Part002
    + surrogateDiagTailX0RatChunk000Sub001Block055Part003
    + surrogateDiagTailX0RatChunk000Sub001Block055Part004
    + surrogateDiagTailX0RatChunk000Sub001Block055Part005
    + surrogateDiagTailX0RatChunk000Sub001Block055Part006
    + surrogateDiagTailX0RatChunk000Sub001Block055Part007
    + surrogateDiagTailX0RatChunk000Sub001Block055Part008
    + surrogateDiagTailX0RatChunk000Sub001Block055Part009
    + surrogateDiagTailX0RatChunk000Sub001Block055Part010
    + surrogateDiagTailX0RatChunk000Sub001Block055Part011
    + surrogateDiagTailX0RatChunk000Sub001Block055Part012
    + surrogateDiagTailX0RatChunk000Sub001Block055Part013
    + surrogateDiagTailX0RatChunk000Sub001Block055Part014
    + surrogateDiagTailX0RatChunk000Sub001Block055Part015
    + surrogateDiagTailX0RatChunk000Sub001Block055Part016
    + surrogateDiagTailX0RatChunk000Sub001Block055Part017
    + surrogateDiagTailX0RatChunk000Sub001Block055Part018
    + surrogateDiagTailX0RatChunk000Sub001Block055Part019
    + surrogateDiagTailX0RatChunk000Sub001Block055Part020
    + surrogateDiagTailX0RatChunk000Sub001Block055Part021
    + surrogateDiagTailX0RatChunk000Sub001Block055Part022
    + surrogateDiagTailX0RatChunk000Sub001Block055Part023
    + surrogateDiagTailX0RatChunk000Sub001Block055Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block055_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block055Head + surrogateDiagTailX0RatChunk000Sub001Block055Mid + surrogateDiagTailX0RatChunk000Sub001Block055Tail =
      surrogateDiagTailX0RatChunk000Sub001Block055 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block055Head surrogateDiagTailX0RatChunk000Sub001Block055Mid surrogateDiagTailX0RatChunk000Sub001Block055Tail surrogateDiagTailX0RatChunk000Sub001Block055
  ring

def SurrogateDiagonalTailChunk000Sub001Block055HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block055HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block055Head

def SurrogateDiagonalTailChunk000Sub001Block055MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block055MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block055Mid

def SurrogateDiagonalTailChunk000Sub001Block055TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block055TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block055Tail

theorem surrogateDiagonalTailChunk000Sub001Block055_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block055HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block055MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block055TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block055Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block055 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block055HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block055MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block055TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block055Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block055_eq_head_add_mid_add_tail

/-- Block 056 covers tail-support indices [6400,6425) and q from 10578 to 10615. -/

def TailChunk000Sub001Block056Part000SupportExplicit : Finset ℕ :=
  ([10578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part000 : ℚ :=
  (443181685 : ℚ) / 127480559173632

def SurrogateDiagonalTailChunk000Sub001Block056Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10578
    = surrogateDiagTailX0RatChunk000Sub001Block056Part000

theorem surrogateDiagonalTailChunk000Sub001Block056Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part000] using hcert

def TailChunk000Sub001Block056Part001SupportExplicit : Finset ℕ :=
  ([10579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part001 : ℚ :=
  (679863301 : ℚ) / 288048674119180800

def SurrogateDiagonalTailChunk000Sub001Block056Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10579
    = surrogateDiagTailX0RatChunk000Sub001Block056Part001

theorem surrogateDiagonalTailChunk000Sub001Block056Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part001] using hcert

def TailChunk000Sub001Block056Part002SupportExplicit : Finset ℕ :=
  ([10581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part002 : ℚ :=
  (18956078725 : ℚ) / 75415778930478144

def SurrogateDiagonalTailChunk000Sub001Block056Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10581
    = surrogateDiagTailX0RatChunk000Sub001Block056Part002

theorem surrogateDiagonalTailChunk000Sub001Block056Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part002] using hcert

def TailChunk000Sub001Block056Part003SupportExplicit : Finset ℕ :=
  ([10582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part003 : ℚ :=
  (11251737383 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk000Sub001Block056Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10582
    = surrogateDiagTailX0RatChunk000Sub001Block056Part003

theorem surrogateDiagonalTailChunk000Sub001Block056Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part003] using hcert

def TailChunk000Sub001Block056Part004SupportExplicit : Finset ℕ :=
  ([10583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part004 : ℚ :=
  (89616294275 : ℚ) / 12542556035210241024

def SurrogateDiagonalTailChunk000Sub001Block056Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10583
    = surrogateDiagTailX0RatChunk000Sub001Block056Part004

theorem surrogateDiagonalTailChunk000Sub001Block056Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part004] using hcert

def TailChunk000Sub001Block056Part005SupportExplicit : Finset ℕ :=
  ([10585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part005 : ℚ :=
  (631860454375 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk000Sub001Block056Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10585
    = surrogateDiagTailX0RatChunk000Sub001Block056Part005

theorem surrogateDiagonalTailChunk000Sub001Block056Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part005] using hcert

def TailChunk000Sub001Block056Part006SupportExplicit : Finset ℕ :=
  ([10586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part006 : ℚ :=
  (106295875825 : ℚ) / 109764279032553288

def SurrogateDiagonalTailChunk000Sub001Block056Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10586
    = surrogateDiagTailX0RatChunk000Sub001Block056Part006

theorem surrogateDiagonalTailChunk000Sub001Block056Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part006] using hcert

def TailChunk000Sub001Block056Part007SupportExplicit : Finset ℕ :=
  ([10587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part007 : ℚ :=
  (778080801275 : ℚ) / 3099068328580890624

def SurrogateDiagonalTailChunk000Sub001Block056Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10587
    = surrogateDiagTailX0RatChunk000Sub001Block056Part007

theorem surrogateDiagonalTailChunk000Sub001Block056Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part007] using hcert

def TailChunk000Sub001Block056Part008SupportExplicit : Finset ℕ :=
  ([10589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block056Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10589
    = surrogateDiagTailX0RatChunk000Sub001Block056Part008

theorem surrogateDiagonalTailChunk000Sub001Block056Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part008] using hcert

def TailChunk000Sub001Block056Part009SupportExplicit : Finset ℕ :=
  ([10590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part009 : ℚ :=
  (900970626175 : ℚ) / 157237981759930368

def SurrogateDiagonalTailChunk000Sub001Block056Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10590
    = surrogateDiagTailX0RatChunk000Sub001Block056Part009

theorem surrogateDiagonalTailChunk000Sub001Block056Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part009] using hcert

def TailChunk000Sub001Block056Part010SupportExplicit : Finset ℕ :=
  ([10591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part010 : ℚ :=
  (281576052425 : ℚ) / 6368138261277179904

def SurrogateDiagonalTailChunk000Sub001Block056Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10591
    = surrogateDiagTailX0RatChunk000Sub001Block056Part010

theorem surrogateDiagonalTailChunk000Sub001Block056Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part010] using hcert

def TailChunk000Sub001Block056Part011SupportExplicit : Finset ℕ :=
  ([10594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part011 : ℚ :=
  (438409515625 : ℚ) / 491766310647570432

def SurrogateDiagonalTailChunk000Sub001Block056Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10594
    = surrogateDiagTailX0RatChunk000Sub001Block056Part011

theorem surrogateDiagonalTailChunk000Sub001Block056Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part011] using hcert

def TailChunk000Sub001Block056Part012SupportExplicit : Finset ℕ :=
  ([10595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part012 : ℚ :=
  (916822347325 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub001Block056Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10595
    = surrogateDiagTailX0RatChunk000Sub001Block056Part012

theorem surrogateDiagonalTailChunk000Sub001Block056Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part012] using hcert

def TailChunk000Sub001Block056Part013SupportExplicit : Finset ℕ :=
  ([10597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block056Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10597
    = surrogateDiagTailX0RatChunk000Sub001Block056Part013

theorem surrogateDiagonalTailChunk000Sub001Block056Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part013] using hcert

def TailChunk000Sub001Block056Part014SupportExplicit : Finset ℕ :=
  ([10598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part014 : ℚ :=
  (3974746675 : ℚ) / 2800446256935936

def SurrogateDiagonalTailChunk000Sub001Block056Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10598
    = surrogateDiagTailX0RatChunk000Sub001Block056Part014

theorem surrogateDiagonalTailChunk000Sub001Block056Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part014] using hcert

def TailChunk000Sub001Block056Part015SupportExplicit : Finset ℕ :=
  ([10599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part015 : ℚ :=
  (1524050975 : ℚ) / 12160730394166884

def SurrogateDiagonalTailChunk000Sub001Block056Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10599
    = surrogateDiagTailX0RatChunk000Sub001Block056Part015

theorem surrogateDiagonalTailChunk000Sub001Block056Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part015] using hcert

def TailChunk000Sub001Block056Part016SupportExplicit : Finset ℕ :=
  ([10601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block056Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10601
    = surrogateDiagTailX0RatChunk000Sub001Block056Part016

theorem surrogateDiagonalTailChunk000Sub001Block056Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part016] using hcert

def TailChunk000Sub001Block056Part017SupportExplicit : Finset ℕ :=
  ([10603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part017 : ℚ :=
  (101365239 : ℚ) / 17484678448709120

def SurrogateDiagonalTailChunk000Sub001Block056Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10603
    = surrogateDiagTailX0RatChunk000Sub001Block056Part017

theorem surrogateDiagonalTailChunk000Sub001Block056Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part017] using hcert

def TailChunk000Sub001Block056Part018SupportExplicit : Finset ℕ :=
  ([10605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part018 : ℚ :=
  (18647214677 : ℚ) / 26547388416000000

def SurrogateDiagonalTailChunk000Sub001Block056Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10605
    = surrogateDiagTailX0RatChunk000Sub001Block056Part018

theorem surrogateDiagonalTailChunk000Sub001Block056Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part018] using hcert

def TailChunk000Sub001Block056Part019SupportExplicit : Finset ℕ :=
  ([10606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part019 : ℚ :=
  (439403265625 : ℚ) / 493998648929801202

def SurrogateDiagonalTailChunk000Sub001Block056Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10606
    = surrogateDiagTailX0RatChunk000Sub001Block056Part019

theorem surrogateDiagonalTailChunk000Sub001Block056Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part019] using hcert

def TailChunk000Sub001Block056Part020SupportExplicit : Finset ℕ :=
  ([10607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block056Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10607
    = surrogateDiagTailX0RatChunk000Sub001Block056Part020

theorem surrogateDiagonalTailChunk000Sub001Block056Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part020] using hcert

def TailChunk000Sub001Block056Part021SupportExplicit : Finset ℕ :=
  ([10610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part021 : ℚ :=
  (26715559037 : ℚ) / 16162937029017600

def SurrogateDiagonalTailChunk000Sub001Block056Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10610
    = surrogateDiagTailX0RatChunk000Sub001Block056Part021

theorem surrogateDiagonalTailChunk000Sub001Block056Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part021] using hcert

def TailChunk000Sub001Block056Part022SupportExplicit : Finset ℕ :=
  ([10613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block056Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10613
    = surrogateDiagTailX0RatChunk000Sub001Block056Part022

theorem surrogateDiagonalTailChunk000Sub001Block056Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part022] using hcert

def TailChunk000Sub001Block056Part023SupportExplicit : Finset ℕ :=
  ([10614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part023 : ℚ :=
  (2962810507 : ℚ) / 849870394490880

def SurrogateDiagonalTailChunk000Sub001Block056Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10614
    = surrogateDiagTailX0RatChunk000Sub001Block056Part023

theorem surrogateDiagonalTailChunk000Sub001Block056Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part023] using hcert

def TailChunk000Sub001Block056Part024SupportExplicit : Finset ℕ :=
  ([10615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block056Part024 : ℚ :=
  (438328069 : ℚ) / 5436905147596800

def SurrogateDiagonalTailChunk000Sub001Block056Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10615
    = surrogateDiagTailX0RatChunk000Sub001Block056Part024

theorem surrogateDiagonalTailChunk000Sub001Block056Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block056Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block056Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block056Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block056Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block056Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block056Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block056HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block056Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block056Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block056Part000
    + surrogateDiagTailX0RatChunk000Sub001Block056Part001
    + surrogateDiagTailX0RatChunk000Sub001Block056Part002
    + surrogateDiagTailX0RatChunk000Sub001Block056Part003
    + surrogateDiagTailX0RatChunk000Sub001Block056Part004
    + surrogateDiagTailX0RatChunk000Sub001Block056Part005
    + surrogateDiagTailX0RatChunk000Sub001Block056Part006
    + surrogateDiagTailX0RatChunk000Sub001Block056Part007
    + surrogateDiagTailX0RatChunk000Sub001Block056Part008
    + surrogateDiagTailX0RatChunk000Sub001Block056Part009

def surrogateDiagonalTailChunk000Sub001Block056MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block056Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block056Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block056Part010
    + surrogateDiagTailX0RatChunk000Sub001Block056Part011
    + surrogateDiagTailX0RatChunk000Sub001Block056Part012
    + surrogateDiagTailX0RatChunk000Sub001Block056Part013
    + surrogateDiagTailX0RatChunk000Sub001Block056Part014
    + surrogateDiagTailX0RatChunk000Sub001Block056Part015
    + surrogateDiagTailX0RatChunk000Sub001Block056Part016
    + surrogateDiagTailX0RatChunk000Sub001Block056Part017
    + surrogateDiagTailX0RatChunk000Sub001Block056Part018
    + surrogateDiagTailX0RatChunk000Sub001Block056Part019

def surrogateDiagonalTailChunk000Sub001Block056TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block056Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block056Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block056Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block056Part020
    + surrogateDiagTailX0RatChunk000Sub001Block056Part021
    + surrogateDiagTailX0RatChunk000Sub001Block056Part022
    + surrogateDiagTailX0RatChunk000Sub001Block056Part023
    + surrogateDiagTailX0RatChunk000Sub001Block056Part024

def surrogateDiagonalTailChunk000Sub001Block056Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block056HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block056MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block056TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block056 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block056Part000
    + surrogateDiagTailX0RatChunk000Sub001Block056Part001
    + surrogateDiagTailX0RatChunk000Sub001Block056Part002
    + surrogateDiagTailX0RatChunk000Sub001Block056Part003
    + surrogateDiagTailX0RatChunk000Sub001Block056Part004
    + surrogateDiagTailX0RatChunk000Sub001Block056Part005
    + surrogateDiagTailX0RatChunk000Sub001Block056Part006
    + surrogateDiagTailX0RatChunk000Sub001Block056Part007
    + surrogateDiagTailX0RatChunk000Sub001Block056Part008
    + surrogateDiagTailX0RatChunk000Sub001Block056Part009
    + surrogateDiagTailX0RatChunk000Sub001Block056Part010
    + surrogateDiagTailX0RatChunk000Sub001Block056Part011
    + surrogateDiagTailX0RatChunk000Sub001Block056Part012
    + surrogateDiagTailX0RatChunk000Sub001Block056Part013
    + surrogateDiagTailX0RatChunk000Sub001Block056Part014
    + surrogateDiagTailX0RatChunk000Sub001Block056Part015
    + surrogateDiagTailX0RatChunk000Sub001Block056Part016
    + surrogateDiagTailX0RatChunk000Sub001Block056Part017
    + surrogateDiagTailX0RatChunk000Sub001Block056Part018
    + surrogateDiagTailX0RatChunk000Sub001Block056Part019
    + surrogateDiagTailX0RatChunk000Sub001Block056Part020
    + surrogateDiagTailX0RatChunk000Sub001Block056Part021
    + surrogateDiagTailX0RatChunk000Sub001Block056Part022
    + surrogateDiagTailX0RatChunk000Sub001Block056Part023
    + surrogateDiagTailX0RatChunk000Sub001Block056Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block056_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block056Head + surrogateDiagTailX0RatChunk000Sub001Block056Mid + surrogateDiagTailX0RatChunk000Sub001Block056Tail =
      surrogateDiagTailX0RatChunk000Sub001Block056 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block056Head surrogateDiagTailX0RatChunk000Sub001Block056Mid surrogateDiagTailX0RatChunk000Sub001Block056Tail surrogateDiagTailX0RatChunk000Sub001Block056
  ring

def SurrogateDiagonalTailChunk000Sub001Block056HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block056HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block056Head

def SurrogateDiagonalTailChunk000Sub001Block056MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block056MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block056Mid

def SurrogateDiagonalTailChunk000Sub001Block056TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block056TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block056Tail

theorem surrogateDiagonalTailChunk000Sub001Block056_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block056HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block056MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block056TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block056Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block056 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block056HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block056MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block056TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block056Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block056_eq_head_add_mid_add_tail

/-- Block 057 covers tail-support indices [6425,6450) and q from 10617 to 10657. -/

def TailChunk000Sub001Block057Part000SupportExplicit : Finset ℕ :=
  ([10617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part000 : ℚ :=
  (391482674525 : ℚ) / 3134354831479892544

def SurrogateDiagonalTailChunk000Sub001Block057Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10617
    = surrogateDiagTailX0RatChunk000Sub001Block057Part000

theorem surrogateDiagonalTailChunk000Sub001Block057Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part000] using hcert

def TailChunk000Sub001Block057Part001SupportExplicit : Finset ℕ :=
  ([10618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part001 : ℚ :=
  (440398140625 : ℚ) / 496238578756737312

def SurrogateDiagonalTailChunk000Sub001Block057Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10618
    = surrogateDiagTailX0RatChunk000Sub001Block057Part001

theorem surrogateDiagonalTailChunk000Sub001Block057Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part001] using hcert

def TailChunk000Sub001Block057Part002SupportExplicit : Finset ℕ :=
  ([10619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part002 : ℚ :=
  (2105619307 : ℚ) / 55736772927160320

def SurrogateDiagonalTailChunk000Sub001Block057Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10619
    = surrogateDiagTailX0RatChunk000Sub001Block057Part002

theorem surrogateDiagonalTailChunk000Sub001Block057Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part002] using hcert

def TailChunk000Sub001Block057Part003SupportExplicit : Finset ℕ :=
  ([10621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part003 : ℚ :=
  (544363675 : ℚ) / 19603123798551552

def SurrogateDiagonalTailChunk000Sub001Block057Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10621
    = surrogateDiagTailX0RatChunk000Sub001Block057Part003

theorem surrogateDiagonalTailChunk000Sub001Block057Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part003] using hcert

def TailChunk000Sub001Block057Part004SupportExplicit : Finset ℕ :=
  ([10622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part004 : ℚ :=
  (243995744725 : ℚ) / 251670456153145344

def SurrogateDiagonalTailChunk000Sub001Block057Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10622
    = surrogateDiagTailX0RatChunk000Sub001Block057Part004

theorem surrogateDiagonalTailChunk000Sub001Block057Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part004] using hcert

def TailChunk000Sub001Block057Part005SupportExplicit : Finset ℕ :=
  ([10623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part005 : ℚ :=
  (783850099 : ℚ) / 6282896270388480

def SurrogateDiagonalTailChunk000Sub001Block057Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10623
    = surrogateDiagTailX0RatChunk000Sub001Block057Part005

theorem surrogateDiagonalTailChunk000Sub001Block057Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part005] using hcert

def TailChunk000Sub001Block057Part006SupportExplicit : Finset ℕ :=
  ([10626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part006 : ℚ :=
  (4327893671 : ℚ) / 607312990310400

def SurrogateDiagonalTailChunk000Sub001Block057Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10626
    = surrogateDiagTailX0RatChunk000Sub001Block057Part006

theorem surrogateDiagonalTailChunk000Sub001Block057Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part006] using hcert

def TailChunk000Sub001Block057Part007SupportExplicit : Finset ℕ :=
  ([10627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block057Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10627
    = surrogateDiagTailX0RatChunk000Sub001Block057Part007

theorem surrogateDiagonalTailChunk000Sub001Block057Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part007] using hcert

def TailChunk000Sub001Block057Part008SupportExplicit : Finset ℕ :=
  ([10630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part008 : ℚ :=
  (705668480375 : ℚ) / 407131678321173504

def SurrogateDiagonalTailChunk000Sub001Block057Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10630
    = surrogateDiagTailX0RatChunk000Sub001Block057Part008

theorem surrogateDiagonalTailChunk000Sub001Block057Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part008] using hcert

def TailChunk000Sub001Block057Part009SupportExplicit : Finset ℕ :=
  ([10631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block057Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10631
    = surrogateDiagTailX0RatChunk000Sub001Block057Part009

theorem surrogateDiagonalTailChunk000Sub001Block057Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part009] using hcert

def TailChunk000Sub001Block057Part010SupportExplicit : Finset ℕ :=
  ([10634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part010 : ℚ :=
  (64162436675 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk000Sub001Block057Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10634
    = surrogateDiagTailX0RatChunk000Sub001Block057Part010

theorem surrogateDiagonalTailChunk000Sub001Block057Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part010] using hcert

def TailChunk000Sub001Block057Part011SupportExplicit : Finset ℕ :=
  ([10635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part011 : ℚ :=
  (293262162875 : ℚ) / 857824770783707136

def SurrogateDiagonalTailChunk000Sub001Block057Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10635
    = surrogateDiagTailX0RatChunk000Sub001Block057Part011

theorem surrogateDiagonalTailChunk000Sub001Block057Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part011] using hcert

def TailChunk000Sub001Block057Part012SupportExplicit : Finset ℕ :=
  ([10637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part012 : ℚ :=
  (78534683 : ℚ) / 5806361842400448

def SurrogateDiagonalTailChunk000Sub001Block057Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10637
    = surrogateDiagTailX0RatChunk000Sub001Block057Part012

theorem surrogateDiagonalTailChunk000Sub001Block057Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part012] using hcert

def TailChunk000Sub001Block057Part013SupportExplicit : Finset ℕ :=
  ([10639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part013 : ℚ :=
  (1768567515625 : ℚ) / 8005838252292172242

def SurrogateDiagonalTailChunk000Sub001Block057Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10639
    = surrogateDiagTailX0RatChunk000Sub001Block057Part013

theorem surrogateDiagonalTailChunk000Sub001Block057Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part013] using hcert

def TailChunk000Sub001Block057Part014SupportExplicit : Finset ℕ :=
  ([10641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part014 : ℚ :=
  (491333100575 : ℚ) / 790700074300461456

def SurrogateDiagonalTailChunk000Sub001Block057Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10641
    = surrogateDiagTailX0RatChunk000Sub001Block057Part014

theorem surrogateDiagonalTailChunk000Sub001Block057Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part014] using hcert

def TailChunk000Sub001Block057Part015SupportExplicit : Finset ℕ :=
  ([10642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part015 : ℚ :=
  (827037375425 : ℚ) / 776417239602561024

def SurrogateDiagonalTailChunk000Sub001Block057Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10642
    = surrogateDiagTailX0RatChunk000Sub001Block057Part015

theorem surrogateDiagonalTailChunk000Sub001Block057Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part015] using hcert

def TailChunk000Sub001Block057Part016SupportExplicit : Finset ℕ :=
  ([10643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part016 : ℚ :=
  (835289864825 : ℚ) / 3447413189275781376

def SurrogateDiagonalTailChunk000Sub001Block057Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10643
    = surrogateDiagTailX0RatChunk000Sub001Block057Part016

theorem surrogateDiagonalTailChunk000Sub001Block057Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part016] using hcert

def TailChunk000Sub001Block057Part017SupportExplicit : Finset ℕ :=
  ([10645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part017 : ℚ :=
  (242689276425 : ℚ) / 625077726591582208

def SurrogateDiagonalTailChunk000Sub001Block057Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10645
    = surrogateDiagTailX0RatChunk000Sub001Block057Part017

theorem surrogateDiagonalTailChunk000Sub001Block057Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part017] using hcert

def TailChunk000Sub001Block057Part018SupportExplicit : Finset ℕ :=
  ([10646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part018 : ℚ :=
  (442723890625 : ℚ) / 501494700966826482

def SurrogateDiagonalTailChunk000Sub001Block057Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10646
    = surrogateDiagTailX0RatChunk000Sub001Block057Part018

theorem surrogateDiagonalTailChunk000Sub001Block057Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part018] using hcert

def TailChunk000Sub001Block057Part019SupportExplicit : Finset ℕ :=
  ([10649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part019 : ℚ :=
  (599804363975 : ℚ) / 2426011187297056128

def SurrogateDiagonalTailChunk000Sub001Block057Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10649
    = surrogateDiagTailX0RatChunk000Sub001Block057Part019

theorem surrogateDiagonalTailChunk000Sub001Block057Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part019] using hcert

def TailChunk000Sub001Block057Part020SupportExplicit : Finset ℕ :=
  ([10651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part020 : ℚ :=
  (113443801 : ℚ) / 514689457558050

def SurrogateDiagonalTailChunk000Sub001Block057Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10651
    = surrogateDiagTailX0RatChunk000Sub001Block057Part020

theorem surrogateDiagonalTailChunk000Sub001Block057Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part020] using hcert

def TailChunk000Sub001Block057Part021SupportExplicit : Finset ℕ :=
  ([10653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part021 : ℚ :=
  (138997477475 : ℚ) / 205575897081544704

def SurrogateDiagonalTailChunk000Sub001Block057Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10653
    = surrogateDiagTailX0RatChunk000Sub001Block057Part021

theorem surrogateDiagonalTailChunk000Sub001Block057Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part021] using hcert

def TailChunk000Sub001Block057Part022SupportExplicit : Finset ℕ :=
  ([10654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part022 : ℚ :=
  (59290438927 : ℚ) / 43246027572019200

def SurrogateDiagonalTailChunk000Sub001Block057Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10654
    = surrogateDiagTailX0RatChunk000Sub001Block057Part022

theorem surrogateDiagonalTailChunk000Sub001Block057Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part022] using hcert

def TailChunk000Sub001Block057Part023SupportExplicit : Finset ℕ :=
  ([10655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part023 : ℚ :=
  (192886411489 : ℚ) / 527042004539443200

def SurrogateDiagonalTailChunk000Sub001Block057Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10655
    = surrogateDiagTailX0RatChunk000Sub001Block057Part023

theorem surrogateDiagonalTailChunk000Sub001Block057Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part023] using hcert

def TailChunk000Sub001Block057Part024SupportExplicit : Finset ℕ :=
  ([10657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block057Part024 : ℚ :=
  (1774557015625 : ℚ) / 8060160963421274112

def SurrogateDiagonalTailChunk000Sub001Block057Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10657
    = surrogateDiagTailX0RatChunk000Sub001Block057Part024

theorem surrogateDiagonalTailChunk000Sub001Block057Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block057Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block057Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block057Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block057Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block057Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block057Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block057HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block057Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block057Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block057Part000
    + surrogateDiagTailX0RatChunk000Sub001Block057Part001
    + surrogateDiagTailX0RatChunk000Sub001Block057Part002
    + surrogateDiagTailX0RatChunk000Sub001Block057Part003
    + surrogateDiagTailX0RatChunk000Sub001Block057Part004
    + surrogateDiagTailX0RatChunk000Sub001Block057Part005
    + surrogateDiagTailX0RatChunk000Sub001Block057Part006
    + surrogateDiagTailX0RatChunk000Sub001Block057Part007
    + surrogateDiagTailX0RatChunk000Sub001Block057Part008
    + surrogateDiagTailX0RatChunk000Sub001Block057Part009

def surrogateDiagonalTailChunk000Sub001Block057MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block057Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block057Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block057Part010
    + surrogateDiagTailX0RatChunk000Sub001Block057Part011
    + surrogateDiagTailX0RatChunk000Sub001Block057Part012
    + surrogateDiagTailX0RatChunk000Sub001Block057Part013
    + surrogateDiagTailX0RatChunk000Sub001Block057Part014
    + surrogateDiagTailX0RatChunk000Sub001Block057Part015
    + surrogateDiagTailX0RatChunk000Sub001Block057Part016
    + surrogateDiagTailX0RatChunk000Sub001Block057Part017
    + surrogateDiagTailX0RatChunk000Sub001Block057Part018
    + surrogateDiagTailX0RatChunk000Sub001Block057Part019

def surrogateDiagonalTailChunk000Sub001Block057TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block057Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block057Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block057Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block057Part020
    + surrogateDiagTailX0RatChunk000Sub001Block057Part021
    + surrogateDiagTailX0RatChunk000Sub001Block057Part022
    + surrogateDiagTailX0RatChunk000Sub001Block057Part023
    + surrogateDiagTailX0RatChunk000Sub001Block057Part024

def surrogateDiagonalTailChunk000Sub001Block057Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block057HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block057MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block057TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block057 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block057Part000
    + surrogateDiagTailX0RatChunk000Sub001Block057Part001
    + surrogateDiagTailX0RatChunk000Sub001Block057Part002
    + surrogateDiagTailX0RatChunk000Sub001Block057Part003
    + surrogateDiagTailX0RatChunk000Sub001Block057Part004
    + surrogateDiagTailX0RatChunk000Sub001Block057Part005
    + surrogateDiagTailX0RatChunk000Sub001Block057Part006
    + surrogateDiagTailX0RatChunk000Sub001Block057Part007
    + surrogateDiagTailX0RatChunk000Sub001Block057Part008
    + surrogateDiagTailX0RatChunk000Sub001Block057Part009
    + surrogateDiagTailX0RatChunk000Sub001Block057Part010
    + surrogateDiagTailX0RatChunk000Sub001Block057Part011
    + surrogateDiagTailX0RatChunk000Sub001Block057Part012
    + surrogateDiagTailX0RatChunk000Sub001Block057Part013
    + surrogateDiagTailX0RatChunk000Sub001Block057Part014
    + surrogateDiagTailX0RatChunk000Sub001Block057Part015
    + surrogateDiagTailX0RatChunk000Sub001Block057Part016
    + surrogateDiagTailX0RatChunk000Sub001Block057Part017
    + surrogateDiagTailX0RatChunk000Sub001Block057Part018
    + surrogateDiagTailX0RatChunk000Sub001Block057Part019
    + surrogateDiagTailX0RatChunk000Sub001Block057Part020
    + surrogateDiagTailX0RatChunk000Sub001Block057Part021
    + surrogateDiagTailX0RatChunk000Sub001Block057Part022
    + surrogateDiagTailX0RatChunk000Sub001Block057Part023
    + surrogateDiagTailX0RatChunk000Sub001Block057Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block057_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block057Head + surrogateDiagTailX0RatChunk000Sub001Block057Mid + surrogateDiagTailX0RatChunk000Sub001Block057Tail =
      surrogateDiagTailX0RatChunk000Sub001Block057 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block057Head surrogateDiagTailX0RatChunk000Sub001Block057Mid surrogateDiagTailX0RatChunk000Sub001Block057Tail surrogateDiagTailX0RatChunk000Sub001Block057
  ring

def SurrogateDiagonalTailChunk000Sub001Block057HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block057HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block057Head

def SurrogateDiagonalTailChunk000Sub001Block057MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block057MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block057Mid

def SurrogateDiagonalTailChunk000Sub001Block057TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block057TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block057Tail

theorem surrogateDiagonalTailChunk000Sub001Block057_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block057HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block057MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block057TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block057Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block057 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block057HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block057MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block057TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block057Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block057_eq_head_add_mid_add_tail

/-- Block 058 covers tail-support indices [6450,6475) and q from 10659 to 10699. -/

def TailChunk000Sub001Block058Part000SupportExplicit : Finset ℕ :=
  ([10659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part000 : ℚ :=
  (39081013099 : ℚ) / 36699109746278400

def SurrogateDiagonalTailChunk000Sub001Block058Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10659
    = surrogateDiagTailX0RatChunk000Sub001Block058Part000

theorem surrogateDiagonalTailChunk000Sub001Block058Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part000] using hcert

def TailChunk000Sub001Block058Part001SupportExplicit : Finset ℕ :=
  ([10661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part001 : ℚ :=
  (43001233625 : ℚ) / 135856524591348921

def SurrogateDiagonalTailChunk000Sub001Block058Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10661
    = surrogateDiagTailX0RatChunk000Sub001Block058Part001

theorem surrogateDiagonalTailChunk000Sub001Block058Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part001] using hcert

def TailChunk000Sub001Block058Part002SupportExplicit : Finset ℕ :=
  ([10662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part002 : ℚ :=
  (39448025 : ℚ) / 13265101651968

def SurrogateDiagonalTailChunk000Sub001Block058Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10662
    = surrogateDiagTailX0RatChunk000Sub001Block058Part002

theorem surrogateDiagonalTailChunk000Sub001Block058Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part002] using hcert

def TailChunk000Sub001Block058Part003SupportExplicit : Finset ℕ :=
  ([10663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part003 : ℚ :=
  (1776555765625 : ℚ) / 8078329817222075442

def SurrogateDiagonalTailChunk000Sub001Block058Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10663
    = surrogateDiagTailX0RatChunk000Sub001Block058Part003

theorem surrogateDiagonalTailChunk000Sub001Block058Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part003] using hcert

def TailChunk000Sub001Block058Part004SupportExplicit : Finset ℕ :=
  ([10666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part004 : ℚ :=
  (444388890625 : ℚ) / 505274557635946272

def SurrogateDiagonalTailChunk000Sub001Block058Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10666
    = surrogateDiagTailX0RatChunk000Sub001Block058Part004

theorem surrogateDiagonalTailChunk000Sub001Block058Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part004] using hcert

def TailChunk000Sub001Block058Part005SupportExplicit : Finset ℕ :=
  ([10667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part005 : ℚ :=
  (1777888890625 : ℚ) / 8090459439437430642

def SurrogateDiagonalTailChunk000Sub001Block058Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10667
    = surrogateDiagTailX0RatChunk000Sub001Block058Part005

theorem surrogateDiagonalTailChunk000Sub001Block058Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part005] using hcert

def TailChunk000Sub001Block058Part006SupportExplicit : Finset ℕ :=
  ([10669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part006 : ℚ :=
  (2278997020125 : ℚ) / 9735778563607662976

def SurrogateDiagonalTailChunk000Sub001Block058Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10669
    = surrogateDiagTailX0RatChunk000Sub001Block058Part006

theorem surrogateDiagonalTailChunk000Sub001Block058Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part006] using hcert

def TailChunk000Sub001Block058Part007SupportExplicit : Finset ℕ :=
  ([10670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part007 : ℚ :=
  (51124059091 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub001Block058Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10670
    = surrogateDiagTailX0RatChunk000Sub001Block058Part007

theorem surrogateDiagonalTailChunk000Sub001Block058Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part007] using hcert

def TailChunk000Sub001Block058Part008SupportExplicit : Finset ℕ :=
  ([10671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part008 : ℚ :=
  (3161908644325 : ℚ) / 6397257774055507968

def SurrogateDiagonalTailChunk000Sub001Block058Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10671
    = surrogateDiagTailX0RatChunk000Sub001Block058Part008

theorem surrogateDiagonalTailChunk000Sub001Block058Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part008] using hcert

def TailChunk000Sub001Block058Part009SupportExplicit : Finset ℕ :=
  ([10673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part009 : ℚ :=
  (250652400229 : ℚ) / 937707185472307200

def SurrogateDiagonalTailChunk000Sub001Block058Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10673
    = surrogateDiagTailX0RatChunk000Sub001Block058Part009

theorem surrogateDiagonalTailChunk000Sub001Block058Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part009] using hcert

def TailChunk000Sub001Block058Part010SupportExplicit : Finset ℕ :=
  ([10677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part010 : ℚ :=
  (3165465644125 : ℚ) / 6411661951354915968

def SurrogateDiagonalTailChunk000Sub001Block058Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10677
    = surrogateDiagTailX0RatChunk000Sub001Block058Part010

theorem surrogateDiagonalTailChunk000Sub001Block058Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part010] using hcert

def TailChunk000Sub001Block058Part011SupportExplicit : Finset ℕ :=
  ([10678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part011 : ℚ :=
  (5589449491 : ℚ) / 5378086090137600

def SurrogateDiagonalTailChunk000Sub001Block058Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10678
    = surrogateDiagTailX0RatChunk000Sub001Block058Part011

theorem surrogateDiagonalTailChunk000Sub001Block058Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part011] using hcert

def TailChunk000Sub001Block058Part012SupportExplicit : Finset ℕ :=
  ([10679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part012 : ℚ :=
  (68857269307 : ℚ) / 297049519048204800

def SurrogateDiagonalTailChunk000Sub001Block058Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10679
    = surrogateDiagTailX0RatChunk000Sub001Block058Part012

theorem surrogateDiagonalTailChunk000Sub001Block058Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part012] using hcert

def TailChunk000Sub001Block058Part013SupportExplicit : Finset ℕ :=
  ([10681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part013 : ℚ :=
  (4119145977 : ℚ) / 14757831142700000

def SurrogateDiagonalTailChunk000Sub001Block058Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10681
    = surrogateDiagTailX0RatChunk000Sub001Block058Part013

theorem surrogateDiagonalTailChunk000Sub001Block058Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part013] using hcert

def TailChunk000Sub001Block058Part014SupportExplicit : Finset ℕ :=
  ([10685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part014 : ℚ :=
  (5134856775325 : ℚ) / 13325141135338242048

def SurrogateDiagonalTailChunk000Sub001Block058Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10685
    = surrogateDiagTailX0RatChunk000Sub001Block058Part014

theorem surrogateDiagonalTailChunk000Sub001Block058Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part014] using hcert

def TailChunk000Sub001Block058Part015SupportExplicit : Finset ℕ :=
  ([10686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part015 : ℚ :=
  (361297442975 : ℚ) / 94603282256756736

def SurrogateDiagonalTailChunk000Sub001Block058Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10686
    = surrogateDiagTailX0RatChunk000Sub001Block058Part015

theorem surrogateDiagonalTailChunk000Sub001Block058Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part015] using hcert

def TailChunk000Sub001Block058Part016SupportExplicit : Finset ℕ :=
  ([10687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part016 : ℚ :=
  (1784562015625 : ℚ) / 8151312570798864402

def SurrogateDiagonalTailChunk000Sub001Block058Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10687
    = surrogateDiagTailX0RatChunk000Sub001Block058Part016

theorem surrogateDiagonalTailChunk000Sub001Block058Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part016] using hcert

def TailChunk000Sub001Block058Part017SupportExplicit : Finset ℕ :=
  ([10689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part017 : ℚ :=
  (95112404525 : ℚ) / 127891867203108864

def SurrogateDiagonalTailChunk000Sub001Block058Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10689
    = surrogateDiagTailX0RatChunk000Sub001Block058Part017

theorem surrogateDiagonalTailChunk000Sub001Block058Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part017] using hcert

def TailChunk000Sub001Block058Part018SupportExplicit : Finset ℕ :=
  ([10690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part018 : ℚ :=
  (713657577875 : ℚ) / 416410660479320064

def SurrogateDiagonalTailChunk000Sub001Block058Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10690
    = surrogateDiagTailX0RatChunk000Sub001Block058Part018

theorem surrogateDiagonalTailChunk000Sub001Block058Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part018] using hcert

def TailChunk000Sub001Block058Part019SupportExplicit : Finset ℕ :=
  ([10691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part019 : ℚ :=
  (2857437025 : ℚ) / 13061638836616242

def SurrogateDiagonalTailChunk000Sub001Block058Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10691
    = surrogateDiagTailX0RatChunk000Sub001Block058Part019

theorem surrogateDiagonalTailChunk000Sub001Block058Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part019] using hcert

def TailChunk000Sub001Block058Part020SupportExplicit : Finset ℕ :=
  ([10694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part020 : ℚ :=
  (446725140625 : ℚ) / 510602204171240082

def SurrogateDiagonalTailChunk000Sub001Block058Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10694
    = surrogateDiagTailX0RatChunk000Sub001Block058Part020

theorem surrogateDiagonalTailChunk000Sub001Block058Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part020] using hcert

def TailChunk000Sub001Block058Part021SupportExplicit : Finset ℕ :=
  ([10695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part021 : ℚ :=
  (7966605203 : ℚ) / 7066914796339200

def SurrogateDiagonalTailChunk000Sub001Block058Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10695
    = surrogateDiagTailX0RatChunk000Sub001Block058Part021

theorem surrogateDiagonalTailChunk000Sub001Block058Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part021] using hcert

def TailChunk000Sub001Block058Part022SupportExplicit : Finset ℕ :=
  ([10697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part022 : ℚ :=
  (6540451827175 : ℚ) / 26185576610368291968

def SurrogateDiagonalTailChunk000Sub001Block058Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10697
    = surrogateDiagTailX0RatChunk000Sub001Block058Part022

theorem surrogateDiagonalTailChunk000Sub001Block058Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part022] using hcert

def TailChunk000Sub001Block058Part023SupportExplicit : Finset ℕ :=
  ([10698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part023 : ℚ :=
  (39714875 : ℚ) / 13445270232768

def SurrogateDiagonalTailChunk000Sub001Block058Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10698
    = surrogateDiagTailX0RatChunk000Sub001Block058Part023

theorem surrogateDiagonalTailChunk000Sub001Block058Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part023] using hcert

def TailChunk000Sub001Block058Part024SupportExplicit : Finset ℕ :=
  ([10699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block058Part024 : ℚ :=
  (699655151075 : ℚ) / 2630247423146330112

def SurrogateDiagonalTailChunk000Sub001Block058Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10699
    = surrogateDiagTailX0RatChunk000Sub001Block058Part024

theorem surrogateDiagonalTailChunk000Sub001Block058Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block058Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block058Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block058Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block058Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block058Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block058Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block058HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block058Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block058Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block058Part000
    + surrogateDiagTailX0RatChunk000Sub001Block058Part001
    + surrogateDiagTailX0RatChunk000Sub001Block058Part002
    + surrogateDiagTailX0RatChunk000Sub001Block058Part003
    + surrogateDiagTailX0RatChunk000Sub001Block058Part004
    + surrogateDiagTailX0RatChunk000Sub001Block058Part005
    + surrogateDiagTailX0RatChunk000Sub001Block058Part006
    + surrogateDiagTailX0RatChunk000Sub001Block058Part007
    + surrogateDiagTailX0RatChunk000Sub001Block058Part008
    + surrogateDiagTailX0RatChunk000Sub001Block058Part009

def surrogateDiagonalTailChunk000Sub001Block058MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block058Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block058Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block058Part010
    + surrogateDiagTailX0RatChunk000Sub001Block058Part011
    + surrogateDiagTailX0RatChunk000Sub001Block058Part012
    + surrogateDiagTailX0RatChunk000Sub001Block058Part013
    + surrogateDiagTailX0RatChunk000Sub001Block058Part014
    + surrogateDiagTailX0RatChunk000Sub001Block058Part015
    + surrogateDiagTailX0RatChunk000Sub001Block058Part016
    + surrogateDiagTailX0RatChunk000Sub001Block058Part017
    + surrogateDiagTailX0RatChunk000Sub001Block058Part018
    + surrogateDiagTailX0RatChunk000Sub001Block058Part019

def surrogateDiagonalTailChunk000Sub001Block058TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block058Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block058Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block058Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block058Part020
    + surrogateDiagTailX0RatChunk000Sub001Block058Part021
    + surrogateDiagTailX0RatChunk000Sub001Block058Part022
    + surrogateDiagTailX0RatChunk000Sub001Block058Part023
    + surrogateDiagTailX0RatChunk000Sub001Block058Part024

def surrogateDiagonalTailChunk000Sub001Block058Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block058HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block058MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block058TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block058 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block058Part000
    + surrogateDiagTailX0RatChunk000Sub001Block058Part001
    + surrogateDiagTailX0RatChunk000Sub001Block058Part002
    + surrogateDiagTailX0RatChunk000Sub001Block058Part003
    + surrogateDiagTailX0RatChunk000Sub001Block058Part004
    + surrogateDiagTailX0RatChunk000Sub001Block058Part005
    + surrogateDiagTailX0RatChunk000Sub001Block058Part006
    + surrogateDiagTailX0RatChunk000Sub001Block058Part007
    + surrogateDiagTailX0RatChunk000Sub001Block058Part008
    + surrogateDiagTailX0RatChunk000Sub001Block058Part009
    + surrogateDiagTailX0RatChunk000Sub001Block058Part010
    + surrogateDiagTailX0RatChunk000Sub001Block058Part011
    + surrogateDiagTailX0RatChunk000Sub001Block058Part012
    + surrogateDiagTailX0RatChunk000Sub001Block058Part013
    + surrogateDiagTailX0RatChunk000Sub001Block058Part014
    + surrogateDiagTailX0RatChunk000Sub001Block058Part015
    + surrogateDiagTailX0RatChunk000Sub001Block058Part016
    + surrogateDiagTailX0RatChunk000Sub001Block058Part017
    + surrogateDiagTailX0RatChunk000Sub001Block058Part018
    + surrogateDiagTailX0RatChunk000Sub001Block058Part019
    + surrogateDiagTailX0RatChunk000Sub001Block058Part020
    + surrogateDiagTailX0RatChunk000Sub001Block058Part021
    + surrogateDiagTailX0RatChunk000Sub001Block058Part022
    + surrogateDiagTailX0RatChunk000Sub001Block058Part023
    + surrogateDiagTailX0RatChunk000Sub001Block058Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block058_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block058Head + surrogateDiagTailX0RatChunk000Sub001Block058Mid + surrogateDiagTailX0RatChunk000Sub001Block058Tail =
      surrogateDiagTailX0RatChunk000Sub001Block058 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block058Head surrogateDiagTailX0RatChunk000Sub001Block058Mid surrogateDiagTailX0RatChunk000Sub001Block058Tail surrogateDiagTailX0RatChunk000Sub001Block058
  ring

def SurrogateDiagonalTailChunk000Sub001Block058HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block058HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block058Head

def SurrogateDiagonalTailChunk000Sub001Block058MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block058MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block058Mid

def SurrogateDiagonalTailChunk000Sub001Block058TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block058TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block058Tail

theorem surrogateDiagonalTailChunk000Sub001Block058_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block058HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block058MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block058TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block058Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block058 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block058HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block058MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block058TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block058Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block058_eq_head_add_mid_add_tail

/-- Block 059 covers tail-support indices [6475,6500) and q from 10702 to 10741. -/

def TailChunk000Sub001Block059Part000SupportExplicit : Finset ℕ :=
  ([10702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part000 : ℚ :=
  (28633201 : ℚ) / 32776454230050

def SurrogateDiagonalTailChunk000Sub001Block059Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10702
    = surrogateDiagTailX0RatChunk000Sub001Block059Part000

theorem surrogateDiagonalTailChunk000Sub001Block059Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part000] using hcert

def TailChunk000Sub001Block059Part001SupportExplicit : Finset ℕ :=
  ([10703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part001 : ℚ :=
  (95792945441 : ℚ) / 235059713070105600

def SurrogateDiagonalTailChunk000Sub001Block059Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10703
    = surrogateDiagTailX0RatChunk000Sub001Block059Part001

theorem surrogateDiagonalTailChunk000Sub001Block059Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part001] using hcert

def TailChunk000Sub001Block059Part002SupportExplicit : Finset ℕ :=
  ([10705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part002 : ℚ :=
  (194701332319 : ℚ) / 537009426105139200

def SurrogateDiagonalTailChunk000Sub001Block059Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10705
    = surrogateDiagTailX0RatChunk000Sub001Block059Part002

theorem surrogateDiagonalTailChunk000Sub001Block059Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part002] using hcert

def TailChunk000Sub001Block059Part003SupportExplicit : Finset ℕ :=
  ([10706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part003 : ℚ :=
  (17371610209 : ℚ) / 18282695808000000

def SurrogateDiagonalTailChunk000Sub001Block059Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10706
    = surrogateDiagTailX0RatChunk000Sub001Block059Part003

theorem surrogateDiagonalTailChunk000Sub001Block059Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part003] using hcert

def TailChunk000Sub001Block059Part004SupportExplicit : Finset ℕ :=
  ([10707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part004 : ℚ :=
  (759991215175 : ℚ) / 1407146845199380992

def SurrogateDiagonalTailChunk000Sub001Block059Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10707
    = surrogateDiagTailX0RatChunk000Sub001Block059Part004

theorem surrogateDiagonalTailChunk000Sub001Block059Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part004] using hcert

def TailChunk000Sub001Block059Part005SupportExplicit : Finset ℕ :=
  ([10709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part005 : ℚ :=
  (1791916890625 : ℚ) / 8218646814481319712

def SurrogateDiagonalTailChunk000Sub001Block059Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10709
    = surrogateDiagTailX0RatChunk000Sub001Block059Part005

theorem surrogateDiagonalTailChunk000Sub001Block059Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part005] using hcert

def TailChunk000Sub001Block059Part006SupportExplicit : Finset ℕ :=
  ([10711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part006 : ℚ :=
  (2868138025 : ℚ) / 13159661962921362

def SurrogateDiagonalTailChunk000Sub001Block059Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10711
    = surrogateDiagTailX0RatChunk000Sub001Block059Part006

theorem surrogateDiagonalTailChunk000Sub001Block059Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part006] using hcert

def TailChunk000Sub001Block059Part007SupportExplicit : Finset ℕ :=
  ([10713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part007 : ℚ :=
  (127473985717 : ℚ) / 259943940008323200

def SurrogateDiagonalTailChunk000Sub001Block059Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10713
    = surrogateDiagTailX0RatChunk000Sub001Block059Part007

theorem surrogateDiagonalTailChunk000Sub001Block059Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part007] using hcert

def TailChunk000Sub001Block059Part008SupportExplicit : Finset ℕ :=
  ([10714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part008 : ℚ :=
  (10750172251 : ℚ) / 9299951354347200

def SurrogateDiagonalTailChunk000Sub001Block059Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10714
    = surrogateDiagTailX0RatChunk000Sub001Block059Part008

theorem surrogateDiagonalTailChunk000Sub001Block059Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part008] using hcert

def TailChunk000Sub001Block059Part009SupportExplicit : Finset ℕ :=
  ([10715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part009 : ℚ :=
  (4876633414525 : ℚ) / 13475493850031474688

def SurrogateDiagonalTailChunk000Sub001Block059Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10715
    = surrogateDiagTailX0RatChunk000Sub001Block059Part009

theorem surrogateDiagonalTailChunk000Sub001Block059Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part009] using hcert

def TailChunk000Sub001Block059Part010SupportExplicit : Finset ℕ :=
  ([10717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part010 : ℚ :=
  (3476345383 : ℚ) / 11098840264438050

def SurrogateDiagonalTailChunk000Sub001Block059Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10717
    = surrogateDiagTailX0RatChunk000Sub001Block059Part010

theorem surrogateDiagonalTailChunk000Sub001Block059Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part010] using hcert

def TailChunk000Sub001Block059Part011SupportExplicit : Finset ℕ :=
  ([10718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part011 : ℚ :=
  (568664026575 : ℚ) / 565650619390590976

def SurrogateDiagonalTailChunk000Sub001Block059Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10718
    = surrogateDiagTailX0RatChunk000Sub001Block059Part011

theorem surrogateDiagonalTailChunk000Sub001Block059Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part011] using hcert

def TailChunk000Sub001Block059Part012SupportExplicit : Finset ℕ :=
  ([10721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part012 : ℚ :=
  (10308204197 : ℚ) / 45027753750000000

def SurrogateDiagonalTailChunk000Sub001Block059Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10721
    = surrogateDiagTailX0RatChunk000Sub001Block059Part012

theorem surrogateDiagonalTailChunk000Sub001Block059Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part012] using hcert

def TailChunk000Sub001Block059Part013SupportExplicit : Finset ℕ :=
  ([10722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part013 : ℚ :=
  (119679825 : ℚ) / 40699194086464

def SurrogateDiagonalTailChunk000Sub001Block059Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10722
    = surrogateDiagTailX0RatChunk000Sub001Block059Part013

theorem surrogateDiagonalTailChunk000Sub001Block059Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part013] using hcert

def TailChunk000Sub001Block059Part014SupportExplicit : Finset ℕ :=
  ([10723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part014 : ℚ :=
  (1796605140625 : ℚ) / 8261712523932776082

def SurrogateDiagonalTailChunk000Sub001Block059Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10723
    = surrogateDiagTailX0RatChunk000Sub001Block059Part014

theorem surrogateDiagonalTailChunk000Sub001Block059Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part014] using hcert

def TailChunk000Sub001Block059Part015SupportExplicit : Finset ℕ :=
  ([10726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part015 : ℚ :=
  (34510324007 : ℚ) / 35453217993753600

def SurrogateDiagonalTailChunk000Sub001Block059Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10726
    = surrogateDiagTailX0RatChunk000Sub001Block059Part015

theorem surrogateDiagonalTailChunk000Sub001Block059Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part015] using hcert

def TailChunk000Sub001Block059Part016SupportExplicit : Finset ℕ :=
  ([10727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part016 : ℚ :=
  (888425543 : ℚ) / 3512219487436800

def SurrogateDiagonalTailChunk000Sub001Block059Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10727
    = surrogateDiagTailX0RatChunk000Sub001Block059Part016

theorem surrogateDiagonalTailChunk000Sub001Block059Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part016] using hcert

def TailChunk000Sub001Block059Part017SupportExplicit : Finset ℕ :=
  ([10729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part017 : ℚ :=
  (1798616265625 : ℚ) / 8280220973752300032

def SurrogateDiagonalTailChunk000Sub001Block059Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10729
    = surrogateDiagTailX0RatChunk000Sub001Block059Part017

theorem surrogateDiagonalTailChunk000Sub001Block059Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part017] using hcert

def TailChunk000Sub001Block059Part018SupportExplicit : Finset ℕ :=
  ([10730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part018 : ℚ :=
  (1346082989725 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub001Block059Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10730
    = surrogateDiagTailX0RatChunk000Sub001Block059Part018

theorem surrogateDiagonalTailChunk000Sub001Block059Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part018] using hcert

def TailChunk000Sub001Block059Part019SupportExplicit : Finset ℕ :=
  ([10733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part019 : ℚ :=
  (1799957640625 : ℚ) / 8292577205103619872

def SurrogateDiagonalTailChunk000Sub001Block059Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10733
    = surrogateDiagTailX0RatChunk000Sub001Block059Part019

theorem surrogateDiagonalTailChunk000Sub001Block059Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part019] using hcert

def TailChunk000Sub001Block059Part020SupportExplicit : Finset ℕ :=
  ([10734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part020 : ℚ :=
  (39982625 : ℚ) / 13627267918848

def SurrogateDiagonalTailChunk000Sub001Block059Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10734
    = surrogateDiagTailX0RatChunk000Sub001Block059Part020

theorem surrogateDiagonalTailChunk000Sub001Block059Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part020] using hcert

def TailChunk000Sub001Block059Part021SupportExplicit : Finset ℕ :=
  ([10735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part021 : ℚ :=
  (4721935107775 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk000Sub001Block059Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10735
    = surrogateDiagTailX0RatChunk000Sub001Block059Part021

theorem surrogateDiagonalTailChunk000Sub001Block059Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part021] using hcert

def TailChunk000Sub001Block059Part022SupportExplicit : Finset ℕ :=
  ([10738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part022 : ℚ :=
  (1391329045975 : ℚ) / 760446768763404288

def SurrogateDiagonalTailChunk000Sub001Block059Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10738
    = surrogateDiagTailX0RatChunk000Sub001Block059Part022

theorem surrogateDiagonalTailChunk000Sub001Block059Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part022] using hcert

def TailChunk000Sub001Block059Part023SupportExplicit : Finset ℕ :=
  ([10739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part023 : ℚ :=
  (1801970640625 : ℚ) / 8311137475095205842

def SurrogateDiagonalTailChunk000Sub001Block059Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10739
    = surrogateDiagTailX0RatChunk000Sub001Block059Part023

theorem surrogateDiagonalTailChunk000Sub001Block059Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part023] using hcert

def TailChunk000Sub001Block059Part024SupportExplicit : Finset ℕ :=
  ([10741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block059Part024 : ℚ :=
  (6712472217325 : ℚ) / 27622389755971579008

def SurrogateDiagonalTailChunk000Sub001Block059Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10741
    = surrogateDiagTailX0RatChunk000Sub001Block059Part024

theorem surrogateDiagonalTailChunk000Sub001Block059Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block059Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block059Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block059Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block059Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block059Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block059Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block059HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block059Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block059Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block059Part000
    + surrogateDiagTailX0RatChunk000Sub001Block059Part001
    + surrogateDiagTailX0RatChunk000Sub001Block059Part002
    + surrogateDiagTailX0RatChunk000Sub001Block059Part003
    + surrogateDiagTailX0RatChunk000Sub001Block059Part004
    + surrogateDiagTailX0RatChunk000Sub001Block059Part005
    + surrogateDiagTailX0RatChunk000Sub001Block059Part006
    + surrogateDiagTailX0RatChunk000Sub001Block059Part007
    + surrogateDiagTailX0RatChunk000Sub001Block059Part008
    + surrogateDiagTailX0RatChunk000Sub001Block059Part009

def surrogateDiagonalTailChunk000Sub001Block059MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block059Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block059Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block059Part010
    + surrogateDiagTailX0RatChunk000Sub001Block059Part011
    + surrogateDiagTailX0RatChunk000Sub001Block059Part012
    + surrogateDiagTailX0RatChunk000Sub001Block059Part013
    + surrogateDiagTailX0RatChunk000Sub001Block059Part014
    + surrogateDiagTailX0RatChunk000Sub001Block059Part015
    + surrogateDiagTailX0RatChunk000Sub001Block059Part016
    + surrogateDiagTailX0RatChunk000Sub001Block059Part017
    + surrogateDiagTailX0RatChunk000Sub001Block059Part018
    + surrogateDiagTailX0RatChunk000Sub001Block059Part019

def surrogateDiagonalTailChunk000Sub001Block059TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block059Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block059Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block059Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block059Part020
    + surrogateDiagTailX0RatChunk000Sub001Block059Part021
    + surrogateDiagTailX0RatChunk000Sub001Block059Part022
    + surrogateDiagTailX0RatChunk000Sub001Block059Part023
    + surrogateDiagTailX0RatChunk000Sub001Block059Part024

def surrogateDiagonalTailChunk000Sub001Block059Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block059HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block059MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block059TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block059 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block059Part000
    + surrogateDiagTailX0RatChunk000Sub001Block059Part001
    + surrogateDiagTailX0RatChunk000Sub001Block059Part002
    + surrogateDiagTailX0RatChunk000Sub001Block059Part003
    + surrogateDiagTailX0RatChunk000Sub001Block059Part004
    + surrogateDiagTailX0RatChunk000Sub001Block059Part005
    + surrogateDiagTailX0RatChunk000Sub001Block059Part006
    + surrogateDiagTailX0RatChunk000Sub001Block059Part007
    + surrogateDiagTailX0RatChunk000Sub001Block059Part008
    + surrogateDiagTailX0RatChunk000Sub001Block059Part009
    + surrogateDiagTailX0RatChunk000Sub001Block059Part010
    + surrogateDiagTailX0RatChunk000Sub001Block059Part011
    + surrogateDiagTailX0RatChunk000Sub001Block059Part012
    + surrogateDiagTailX0RatChunk000Sub001Block059Part013
    + surrogateDiagTailX0RatChunk000Sub001Block059Part014
    + surrogateDiagTailX0RatChunk000Sub001Block059Part015
    + surrogateDiagTailX0RatChunk000Sub001Block059Part016
    + surrogateDiagTailX0RatChunk000Sub001Block059Part017
    + surrogateDiagTailX0RatChunk000Sub001Block059Part018
    + surrogateDiagTailX0RatChunk000Sub001Block059Part019
    + surrogateDiagTailX0RatChunk000Sub001Block059Part020
    + surrogateDiagTailX0RatChunk000Sub001Block059Part021
    + surrogateDiagTailX0RatChunk000Sub001Block059Part022
    + surrogateDiagTailX0RatChunk000Sub001Block059Part023
    + surrogateDiagTailX0RatChunk000Sub001Block059Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block059_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block059Head + surrogateDiagTailX0RatChunk000Sub001Block059Mid + surrogateDiagTailX0RatChunk000Sub001Block059Tail =
      surrogateDiagTailX0RatChunk000Sub001Block059 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block059Head surrogateDiagTailX0RatChunk000Sub001Block059Mid surrogateDiagTailX0RatChunk000Sub001Block059Tail surrogateDiagTailX0RatChunk000Sub001Block059
  ring

def SurrogateDiagonalTailChunk000Sub001Block059HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block059HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block059Head

def SurrogateDiagonalTailChunk000Sub001Block059MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block059MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block059Mid

def SurrogateDiagonalTailChunk000Sub001Block059TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block059TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block059Tail

theorem surrogateDiagonalTailChunk000Sub001Block059_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block059HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block059MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block059TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block059Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block059 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block059HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block059MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block059TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block059Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block059_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
