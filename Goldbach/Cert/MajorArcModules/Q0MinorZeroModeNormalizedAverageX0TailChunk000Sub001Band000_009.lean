import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [0,10). -/

/-- Block 000 covers tail-support indices [5000,5025) and q from 8270 to 8311. -/

def TailChunk000Sub001Block000Part000SupportExplicit : Finset ℕ :=
  ([8270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part000 : ℚ :=
  (768270284375 : ℚ) / 148989964890891264

def SurrogateDiagonalTailChunk000Sub001Block000Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8270
    = surrogateDiagTailX0RatChunk000Sub001Block000Part000

theorem surrogateDiagonalTailChunk000Sub001Block000Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part000] using hcert

def TailChunk000Sub001Block000Part001SupportExplicit : Finset ℕ :=
  ([8273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part001 : ℚ :=
  (1069414515625 : ℚ) / 2926907318390956032

def SurrogateDiagonalTailChunk000Sub001Block000Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8273
    = surrogateDiagTailX0RatChunk000Sub001Block000Part001

theorem surrogateDiagonalTailChunk000Sub001Block000Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part001] using hcert

def TailChunk000Sub001Block000Part002SupportExplicit : Finset ℕ :=
  ([8274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part002 : ℚ :=
  (3958049925 : ℚ) / 314897965613056

def SurrogateDiagonalTailChunk000Sub001Block000Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8274
    = surrogateDiagTailX0RatChunk000Sub001Block000Part002

theorem surrogateDiagonalTailChunk000Sub001Block000Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part002] using hcert

def TailChunk000Sub001Block000Part003SupportExplicit : Finset ℕ :=
  ([8277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part003 : ℚ :=
  (89983937941 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk000Sub001Block000Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8277
    = surrogateDiagTailX0RatChunk000Sub001Block000Part003

theorem surrogateDiagonalTailChunk000Sub001Block000Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part003] using hcert

def TailChunk000Sub001Block000Part004SupportExplicit : Finset ℕ :=
  ([8278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part004 : ℚ :=
  (2140986841975 : ℚ) / 733143188882752968

def SurrogateDiagonalTailChunk000Sub001Block000Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8278
    = surrogateDiagTailX0RatChunk000Sub001Block000Part004

theorem surrogateDiagonalTailChunk000Sub001Block000Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part004] using hcert

def TailChunk000Sub001Block000Part005SupportExplicit : Finset ℕ :=
  ([8279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part005 : ℚ :=
  (4761077825 : ℚ) / 285694505605545984

def SurrogateDiagonalTailChunk000Sub001Block000Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8279
    = surrogateDiagTailX0RatChunk000Sub001Block000Part005

theorem surrogateDiagonalTailChunk000Sub001Block000Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part005] using hcert

def TailChunk000Sub001Block000Part006SupportExplicit : Finset ℕ :=
  ([8282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part006 : ℚ :=
  (8345801033 : ℚ) / 5121024000000000

def SurrogateDiagonalTailChunk000Sub001Block000Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8282
    = surrogateDiagTailX0RatChunk000Sub001Block000Part006

theorem surrogateDiagonalTailChunk000Sub001Block000Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part006] using hcert

def TailChunk000Sub001Block000Part007SupportExplicit : Finset ℕ :=
  ([8283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part007 : ℚ :=
  (21501259807 : ℚ) / 62512500000000000

def SurrogateDiagonalTailChunk000Sub001Block000Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8283
    = surrogateDiagTailX0RatChunk000Sub001Block000Part007

theorem surrogateDiagonalTailChunk000Sub001Block000Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part007] using hcert

def TailChunk000Sub001Block000Part008SupportExplicit : Finset ℕ :=
  ([8285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part008 : ℚ :=
  (257616258725 : ℚ) / 2407011461837881344

def SurrogateDiagonalTailChunk000Sub001Block000Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8285
    = surrogateDiagTailX0RatChunk000Sub001Block000Part008

theorem surrogateDiagonalTailChunk000Sub001Block000Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part008] using hcert

def TailChunk000Sub001Block000Part009SupportExplicit : Finset ℕ :=
  ([8286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part009 : ℚ :=
  (953033 : ℚ) / 193426099200

def SurrogateDiagonalTailChunk000Sub001Block000Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8286
    = surrogateDiagTailX0RatChunk000Sub001Block000Part009

theorem surrogateDiagonalTailChunk000Sub001Block000Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part009] using hcert

def TailChunk000Sub001Block000Part010SupportExplicit : Finset ℕ :=
  ([8287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block000Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8287
    = surrogateDiagTailX0RatChunk000Sub001Block000Part010

theorem surrogateDiagonalTailChunk000Sub001Block000Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part010] using hcert

def TailChunk000Sub001Block000Part011SupportExplicit : Finset ℕ :=
  ([8290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part011 : ℚ :=
  (901250229625 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub001Block000Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8290
    = surrogateDiagTailX0RatChunk000Sub001Block000Part011

theorem surrogateDiagonalTailChunk000Sub001Block000Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part011] using hcert

def TailChunk000Sub001Block000Part012SupportExplicit : Finset ℕ :=
  ([8291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block000Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8291
    = surrogateDiagTailX0RatChunk000Sub001Block000Part012

theorem surrogateDiagonalTailChunk000Sub001Block000Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part012] using hcert

def TailChunk000Sub001Block000Part013SupportExplicit : Finset ℕ :=
  ([8293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block000Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8293
    = surrogateDiagTailX0RatChunk000Sub001Block000Part013

theorem surrogateDiagonalTailChunk000Sub001Block000Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part013] using hcert

def TailChunk000Sub001Block000Part014SupportExplicit : Finset ℕ :=
  ([8294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part014 : ℚ :=
  (18148531529 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub001Block000Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8294
    = surrogateDiagTailX0RatChunk000Sub001Block000Part014

theorem surrogateDiagonalTailChunk000Sub001Block000Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part014] using hcert

def TailChunk000Sub001Block000Part015SupportExplicit : Finset ℕ :=
  ([8295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part015 : ℚ :=
  (861004289875 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk000Sub001Block000Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8295
    = surrogateDiagTailX0RatChunk000Sub001Block000Part015

theorem surrogateDiagonalTailChunk000Sub001Block000Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part015] using hcert

def TailChunk000Sub001Block000Part016SupportExplicit : Finset ℕ :=
  ([8297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block000Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8297
    = surrogateDiagTailX0RatChunk000Sub001Block000Part016

theorem surrogateDiagonalTailChunk000Sub001Block000Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part016] using hcert

def TailChunk000Sub001Block000Part017SupportExplicit : Finset ℕ :=
  ([8299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part017 : ℚ :=
  (72802967575 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk000Sub001Block000Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8299
    = surrogateDiagTailX0RatChunk000Sub001Block000Part017

theorem surrogateDiagonalTailChunk000Sub001Block000Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part017] using hcert

def TailChunk000Sub001Block000Part018SupportExplicit : Finset ℕ :=
  ([8301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part018 : ℚ :=
  (478389039725 : ℚ) / 1170915483700206144

def SurrogateDiagonalTailChunk000Sub001Block000Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8301
    = surrogateDiagTailX0RatChunk000Sub001Block000Part018

theorem surrogateDiagonalTailChunk000Sub001Block000Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part018] using hcert

def TailChunk000Sub001Block000Part019SupportExplicit : Finset ℕ :=
  ([8302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part019 : ℚ :=
  (235982036875 : ℚ) / 99508160042237952

def SurrogateDiagonalTailChunk000Sub001Block000Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8302
    = surrogateDiagTailX0RatChunk000Sub001Block000Part019

theorem surrogateDiagonalTailChunk000Sub001Block000Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part019] using hcert

def TailChunk000Sub001Block000Part020SupportExplicit : Finset ℕ :=
  ([8305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part020 : ℚ :=
  (482380451 : ℚ) / 2592518400000000

def SurrogateDiagonalTailChunk000Sub001Block000Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8305
    = surrogateDiagTailX0RatChunk000Sub001Block000Part020

theorem surrogateDiagonalTailChunk000Sub001Block000Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part020] using hcert

def TailChunk000Sub001Block000Part021SupportExplicit : Finset ℕ :=
  ([8306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part021 : ℚ :=
  (269490765625 : ℚ) / 185778840040100352

def SurrogateDiagonalTailChunk000Sub001Block000Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8306
    = surrogateDiagTailX0RatChunk000Sub001Block000Part021

theorem surrogateDiagonalTailChunk000Sub001Block000Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part021] using hcert

def TailChunk000Sub001Block000Part022SupportExplicit : Finset ℕ :=
  ([8309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part022 : ℚ :=
  (353312454325 : ℚ) / 6411661951354915968

def SurrogateDiagonalTailChunk000Sub001Block000Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8309
    = surrogateDiagTailX0RatChunk000Sub001Block000Part022

theorem surrogateDiagonalTailChunk000Sub001Block000Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part022] using hcert

def TailChunk000Sub001Block000Part023SupportExplicit : Finset ℕ :=
  ([8310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part023 : ℚ :=
  (37656170275 : ℚ) / 3714523860860928

def SurrogateDiagonalTailChunk000Sub001Block000Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8310
    = surrogateDiagTailX0RatChunk000Sub001Block000Part023

theorem surrogateDiagonalTailChunk000Sub001Block000Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part023] using hcert

def TailChunk000Sub001Block000Part024SupportExplicit : Finset ℕ :=
  ([8311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block000Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block000Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8311
    = surrogateDiagTailX0RatChunk000Sub001Block000Part024

theorem surrogateDiagonalTailChunk000Sub001Block000Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block000Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block000Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block000Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block000Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block000Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block000Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block000HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block000Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block000Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block000Part000
    + surrogateDiagTailX0RatChunk000Sub001Block000Part001
    + surrogateDiagTailX0RatChunk000Sub001Block000Part002
    + surrogateDiagTailX0RatChunk000Sub001Block000Part003
    + surrogateDiagTailX0RatChunk000Sub001Block000Part004
    + surrogateDiagTailX0RatChunk000Sub001Block000Part005
    + surrogateDiagTailX0RatChunk000Sub001Block000Part006
    + surrogateDiagTailX0RatChunk000Sub001Block000Part007
    + surrogateDiagTailX0RatChunk000Sub001Block000Part008
    + surrogateDiagTailX0RatChunk000Sub001Block000Part009

def surrogateDiagonalTailChunk000Sub001Block000MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block000Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block000Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block000Part010
    + surrogateDiagTailX0RatChunk000Sub001Block000Part011
    + surrogateDiagTailX0RatChunk000Sub001Block000Part012
    + surrogateDiagTailX0RatChunk000Sub001Block000Part013
    + surrogateDiagTailX0RatChunk000Sub001Block000Part014
    + surrogateDiagTailX0RatChunk000Sub001Block000Part015
    + surrogateDiagTailX0RatChunk000Sub001Block000Part016
    + surrogateDiagTailX0RatChunk000Sub001Block000Part017
    + surrogateDiagTailX0RatChunk000Sub001Block000Part018
    + surrogateDiagTailX0RatChunk000Sub001Block000Part019

def surrogateDiagonalTailChunk000Sub001Block000TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block000Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block000Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block000Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block000Part020
    + surrogateDiagTailX0RatChunk000Sub001Block000Part021
    + surrogateDiagTailX0RatChunk000Sub001Block000Part022
    + surrogateDiagTailX0RatChunk000Sub001Block000Part023
    + surrogateDiagTailX0RatChunk000Sub001Block000Part024

def surrogateDiagonalTailChunk000Sub001Block000Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block000HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block000MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block000TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block000 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block000Part000
    + surrogateDiagTailX0RatChunk000Sub001Block000Part001
    + surrogateDiagTailX0RatChunk000Sub001Block000Part002
    + surrogateDiagTailX0RatChunk000Sub001Block000Part003
    + surrogateDiagTailX0RatChunk000Sub001Block000Part004
    + surrogateDiagTailX0RatChunk000Sub001Block000Part005
    + surrogateDiagTailX0RatChunk000Sub001Block000Part006
    + surrogateDiagTailX0RatChunk000Sub001Block000Part007
    + surrogateDiagTailX0RatChunk000Sub001Block000Part008
    + surrogateDiagTailX0RatChunk000Sub001Block000Part009
    + surrogateDiagTailX0RatChunk000Sub001Block000Part010
    + surrogateDiagTailX0RatChunk000Sub001Block000Part011
    + surrogateDiagTailX0RatChunk000Sub001Block000Part012
    + surrogateDiagTailX0RatChunk000Sub001Block000Part013
    + surrogateDiagTailX0RatChunk000Sub001Block000Part014
    + surrogateDiagTailX0RatChunk000Sub001Block000Part015
    + surrogateDiagTailX0RatChunk000Sub001Block000Part016
    + surrogateDiagTailX0RatChunk000Sub001Block000Part017
    + surrogateDiagTailX0RatChunk000Sub001Block000Part018
    + surrogateDiagTailX0RatChunk000Sub001Block000Part019
    + surrogateDiagTailX0RatChunk000Sub001Block000Part020
    + surrogateDiagTailX0RatChunk000Sub001Block000Part021
    + surrogateDiagTailX0RatChunk000Sub001Block000Part022
    + surrogateDiagTailX0RatChunk000Sub001Block000Part023
    + surrogateDiagTailX0RatChunk000Sub001Block000Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block000_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block000Head + surrogateDiagTailX0RatChunk000Sub001Block000Mid + surrogateDiagTailX0RatChunk000Sub001Block000Tail =
      surrogateDiagTailX0RatChunk000Sub001Block000 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block000Head surrogateDiagTailX0RatChunk000Sub001Block000Mid surrogateDiagTailX0RatChunk000Sub001Block000Tail surrogateDiagTailX0RatChunk000Sub001Block000
  ring

def SurrogateDiagonalTailChunk000Sub001Block000HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block000HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block000Head

def SurrogateDiagonalTailChunk000Sub001Block000MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block000MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block000Mid

def SurrogateDiagonalTailChunk000Sub001Block000TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block000TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block000Tail

theorem surrogateDiagonalTailChunk000Sub001Block000_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block000HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block000MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block000TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block000Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block000 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block000HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block000MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block000TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block000Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block000_eq_head_add_mid_add_tail

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

/-- Block 002 covers tail-support indices [5050,5075) and q from 8354 to 8393. -/

def TailChunk000Sub001Block002Part000SupportExplicit : Finset ℕ :=
  ([8354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part000 : ℚ :=
  (272614515625 : ℚ) / 190111692190851072

def SurrogateDiagonalTailChunk000Sub001Block002Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8354
    = surrogateDiagTailX0RatChunk000Sub001Block002Part000

theorem surrogateDiagonalTailChunk000Sub001Block002Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part000] using hcert

def TailChunk000Sub001Block002Part001SupportExplicit : Finset ℕ :=
  ([8355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part001 : ℚ :=
  (899804765825 : ℚ) / 489390999087611904

def SurrogateDiagonalTailChunk000Sub001Block002Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8355
    = surrogateDiagTailX0RatChunk000Sub001Block002Part001

theorem surrogateDiagonalTailChunk000Sub001Block002Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part001] using hcert

def TailChunk000Sub001Block002Part002SupportExplicit : Finset ℕ :=
  ([8357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part002 : ℚ :=
  (33779643857 : ℚ) / 88690577115709440

def SurrogateDiagonalTailChunk000Sub001Block002Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8357
    = surrogateDiagTailX0RatChunk000Sub001Block002Part002

theorem surrogateDiagonalTailChunk000Sub001Block002Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part002] using hcert

def TailChunk000Sub001Block002Part003SupportExplicit : Finset ℕ :=
  ([8358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part003 : ℚ :=
  (3657732325 : ℚ) / 402482881760256

def SurrogateDiagonalTailChunk000Sub001Block002Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8358
    = surrogateDiagTailX0RatChunk000Sub001Block002Part003

theorem surrogateDiagonalTailChunk000Sub001Block002Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part003] using hcert

def TailChunk000Sub001Block002Part004SupportExplicit : Finset ℕ :=
  ([8359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part004 : ℚ :=
  (1947095819675 : ℚ) / 4404148555844772864

def SurrogateDiagonalTailChunk000Sub001Block002Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8359
    = surrogateDiagTailX0RatChunk000Sub001Block002Part004

theorem surrogateDiagonalTailChunk000Sub001Block002Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part004] using hcert

def TailChunk000Sub001Block002Part005SupportExplicit : Finset ℕ :=
  ([8362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part005 : ℚ :=
  (1061917638025 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub001Block002Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8362
    = surrogateDiagTailX0RatChunk000Sub001Block002Part005

theorem surrogateDiagonalTailChunk000Sub001Block002Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part005] using hcert

def TailChunk000Sub001Block002Part006SupportExplicit : Finset ℕ :=
  ([8363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part006 : ℚ :=
  (1092808890625 : ℚ) / 3056381205401488242

def SurrogateDiagonalTailChunk000Sub001Block002Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8363
    = surrogateDiagTailX0RatChunk000Sub001Block002Part006

theorem surrogateDiagonalTailChunk000Sub001Block002Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part006] using hcert

def TailChunk000Sub001Block002Part007SupportExplicit : Finset ℕ :=
  ([8365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part007 : ℚ :=
  (2521402699525 : ℚ) / 2661825945685229568

def SurrogateDiagonalTailChunk000Sub001Block002Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8365
    = surrogateDiagTailX0RatChunk000Sub001Block002Part007

theorem surrogateDiagonalTailChunk000Sub001Block002Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part007] using hcert

def TailChunk000Sub001Block002Part008SupportExplicit : Finset ℕ :=
  ([8366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part008 : ℚ :=
  (1065640291825 : ℚ) / 671411652430430208

def SurrogateDiagonalTailChunk000Sub001Block002Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8366
    = surrogateDiagTailX0RatChunk000Sub001Block002Part008

theorem surrogateDiagonalTailChunk000Sub001Block002Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part008] using hcert

def TailChunk000Sub001Block002Part009SupportExplicit : Finset ℕ :=
  ([8367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part009 : ℚ :=
  (1215029257475 : ℚ) / 1208614843176428544

def SurrogateDiagonalTailChunk000Sub001Block002Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8367
    = surrogateDiagTailX0RatChunk000Sub001Block002Part009

theorem surrogateDiagonalTailChunk000Sub001Block002Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part009] using hcert

def TailChunk000Sub001Block002Part010SupportExplicit : Finset ℕ :=
  ([8369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part010 : ℚ :=
  (1094377515625 : ℚ) / 3065162852915945472

def SurrogateDiagonalTailChunk000Sub001Block002Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8369
    = surrogateDiagTailX0RatChunk000Sub001Block002Part010

theorem surrogateDiagonalTailChunk000Sub001Block002Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part010] using hcert

def TailChunk000Sub001Block002Part011SupportExplicit : Finset ℕ :=
  ([8371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part011 : ℚ :=
  (5058932589 : ℚ) / 11122949478400000

def SurrogateDiagonalTailChunk000Sub001Block002Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8371
    = surrogateDiagTailX0RatChunk000Sub001Block002Part011

theorem surrogateDiagonalTailChunk000Sub001Block002Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part011] using hcert

def TailChunk000Sub001Block002Part012SupportExplicit : Finset ℕ :=
  ([8373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part012 : ℚ :=
  (77865988837 : ℚ) / 96966930004099200

def SurrogateDiagonalTailChunk000Sub001Block002Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8373
    = surrogateDiagTailX0RatChunk000Sub001Block002Part012

theorem surrogateDiagonalTailChunk000Sub001Block002Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part012] using hcert

def TailChunk000Sub001Block002Part013SupportExplicit : Finset ℕ :=
  ([8374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part013 : ℚ :=
  (534082677425 : ℚ) / 338367504582042624

def SurrogateDiagonalTailChunk000Sub001Block002Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8374
    = surrogateDiagTailX0RatChunk000Sub001Block002Part013

theorem surrogateDiagonalTailChunk000Sub001Block002Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part013] using hcert

def TailChunk000Sub001Block002Part014SupportExplicit : Finset ℕ :=
  ([8377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part014 : ℚ :=
  (1096470765625 : ℚ) / 3076901136679260672

def SurrogateDiagonalTailChunk000Sub001Block002Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8377
    = surrogateDiagTailX0RatChunk000Sub001Block002Part014

theorem surrogateDiagonalTailChunk000Sub001Block002Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part014] using hcert

def TailChunk000Sub001Block002Part015SupportExplicit : Finset ℕ :=
  ([8378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part015 : ℚ :=
  (2037192669 : ℚ) / 1294111479875200

def SurrogateDiagonalTailChunk000Sub001Block002Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8378
    = surrogateDiagTailX0RatChunk000Sub001Block002Part015

theorem surrogateDiagonalTailChunk000Sub001Block002Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part015] using hcert

def TailChunk000Sub001Block002Part016SupportExplicit : Finset ℕ :=
  ([8382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part016 : ℚ :=
  (7713679669 : ℚ) / 1008391141900800

def SurrogateDiagonalTailChunk000Sub001Block002Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8382
    = surrogateDiagTailX0RatChunk000Sub001Block002Part016

theorem surrogateDiagonalTailChunk000Sub001Block002Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part016] using hcert

def TailChunk000Sub001Block002Part017SupportExplicit : Finset ℕ :=
  ([8383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part017 : ℚ :=
  (28392910191 : ℚ) / 75368697392000000

def SurrogateDiagonalTailChunk000Sub001Block002Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8383
    = surrogateDiagTailX0RatChunk000Sub001Block002Part017

theorem surrogateDiagonalTailChunk000Sub001Block002Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part017] using hcert

def TailChunk000Sub001Block002Part018SupportExplicit : Finset ℕ :=
  ([8385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part018 : ℚ :=
  (796910850275 : ℚ) / 330429609378054144

def SurrogateDiagonalTailChunk000Sub001Block002Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8385
    = surrogateDiagTailX0RatChunk000Sub001Block002Part018

theorem surrogateDiagonalTailChunk000Sub001Block002Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part018] using hcert

def TailChunk000Sub001Block002Part019SupportExplicit : Finset ℕ :=
  ([8386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part019 : ℚ :=
  (985461893725 : ℚ) / 414416078086128768

def SurrogateDiagonalTailChunk000Sub001Block002Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8386
    = surrogateDiagTailX0RatChunk000Sub001Block002Part019

theorem surrogateDiagonalTailChunk000Sub001Block002Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part019] using hcert

def TailChunk000Sub001Block002Part020SupportExplicit : Finset ℕ :=
  ([8387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part020 : ℚ :=
  (1099090140625 : ℚ) / 3091621364632810002

def SurrogateDiagonalTailChunk000Sub001Block002Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8387
    = surrogateDiagTailX0RatChunk000Sub001Block002Part020

theorem surrogateDiagonalTailChunk000Sub001Block002Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part020] using hcert

def TailChunk000Sub001Block002Part021SupportExplicit : Finset ℕ :=
  ([8389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part021 : ℚ :=
  (1099614390625 : ℚ) / 3094571736714184992

def SurrogateDiagonalTailChunk000Sub001Block002Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8389
    = surrogateDiagTailX0RatChunk000Sub001Block002Part021

theorem surrogateDiagonalTailChunk000Sub001Block002Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part021] using hcert

def TailChunk000Sub001Block002Part022SupportExplicit : Finset ℕ :=
  ([8390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part022 : ℚ :=
  (307706881125 : ℚ) / 105225656504129536

def SurrogateDiagonalTailChunk000Sub001Block002Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8390
    = surrogateDiagTailX0RatChunk000Sub001Block002Part022

theorem surrogateDiagonalTailChunk000Sub001Block002Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part022] using hcert

def TailChunk000Sub001Block002Part023SupportExplicit : Finset ℕ :=
  ([8391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part023 : ℚ :=
  (1222010374175 : ℚ) / 1222546858948813824

def SurrogateDiagonalTailChunk000Sub001Block002Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8391
    = surrogateDiagTailX0RatChunk000Sub001Block002Part023

theorem surrogateDiagonalTailChunk000Sub001Block002Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part023] using hcert

def TailChunk000Sub001Block002Part024SupportExplicit : Finset ℕ :=
  ([8393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block002Part024 : ℚ :=
  (60404058983 : ℚ) / 88177316544921600

def SurrogateDiagonalTailChunk000Sub001Block002Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8393
    = surrogateDiagTailX0RatChunk000Sub001Block002Part024

theorem surrogateDiagonalTailChunk000Sub001Block002Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block002Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block002Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block002Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block002Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block002Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block002HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block002Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block002Part000
    + surrogateDiagTailX0RatChunk000Sub001Block002Part001
    + surrogateDiagTailX0RatChunk000Sub001Block002Part002
    + surrogateDiagTailX0RatChunk000Sub001Block002Part003
    + surrogateDiagTailX0RatChunk000Sub001Block002Part004
    + surrogateDiagTailX0RatChunk000Sub001Block002Part005
    + surrogateDiagTailX0RatChunk000Sub001Block002Part006
    + surrogateDiagTailX0RatChunk000Sub001Block002Part007
    + surrogateDiagTailX0RatChunk000Sub001Block002Part008
    + surrogateDiagTailX0RatChunk000Sub001Block002Part009

def surrogateDiagonalTailChunk000Sub001Block002MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block002Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block002Part010
    + surrogateDiagTailX0RatChunk000Sub001Block002Part011
    + surrogateDiagTailX0RatChunk000Sub001Block002Part012
    + surrogateDiagTailX0RatChunk000Sub001Block002Part013
    + surrogateDiagTailX0RatChunk000Sub001Block002Part014
    + surrogateDiagTailX0RatChunk000Sub001Block002Part015
    + surrogateDiagTailX0RatChunk000Sub001Block002Part016
    + surrogateDiagTailX0RatChunk000Sub001Block002Part017
    + surrogateDiagTailX0RatChunk000Sub001Block002Part018
    + surrogateDiagTailX0RatChunk000Sub001Block002Part019

def surrogateDiagonalTailChunk000Sub001Block002TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block002Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block002Part020
    + surrogateDiagTailX0RatChunk000Sub001Block002Part021
    + surrogateDiagTailX0RatChunk000Sub001Block002Part022
    + surrogateDiagTailX0RatChunk000Sub001Block002Part023
    + surrogateDiagTailX0RatChunk000Sub001Block002Part024

def surrogateDiagonalTailChunk000Sub001Block002Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block002HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block002MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block002TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block002 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block002Part000
    + surrogateDiagTailX0RatChunk000Sub001Block002Part001
    + surrogateDiagTailX0RatChunk000Sub001Block002Part002
    + surrogateDiagTailX0RatChunk000Sub001Block002Part003
    + surrogateDiagTailX0RatChunk000Sub001Block002Part004
    + surrogateDiagTailX0RatChunk000Sub001Block002Part005
    + surrogateDiagTailX0RatChunk000Sub001Block002Part006
    + surrogateDiagTailX0RatChunk000Sub001Block002Part007
    + surrogateDiagTailX0RatChunk000Sub001Block002Part008
    + surrogateDiagTailX0RatChunk000Sub001Block002Part009
    + surrogateDiagTailX0RatChunk000Sub001Block002Part010
    + surrogateDiagTailX0RatChunk000Sub001Block002Part011
    + surrogateDiagTailX0RatChunk000Sub001Block002Part012
    + surrogateDiagTailX0RatChunk000Sub001Block002Part013
    + surrogateDiagTailX0RatChunk000Sub001Block002Part014
    + surrogateDiagTailX0RatChunk000Sub001Block002Part015
    + surrogateDiagTailX0RatChunk000Sub001Block002Part016
    + surrogateDiagTailX0RatChunk000Sub001Block002Part017
    + surrogateDiagTailX0RatChunk000Sub001Block002Part018
    + surrogateDiagTailX0RatChunk000Sub001Block002Part019
    + surrogateDiagTailX0RatChunk000Sub001Block002Part020
    + surrogateDiagTailX0RatChunk000Sub001Block002Part021
    + surrogateDiagTailX0RatChunk000Sub001Block002Part022
    + surrogateDiagTailX0RatChunk000Sub001Block002Part023
    + surrogateDiagTailX0RatChunk000Sub001Block002Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block002_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block002Head + surrogateDiagTailX0RatChunk000Sub001Block002Mid + surrogateDiagTailX0RatChunk000Sub001Block002Tail =
      surrogateDiagTailX0RatChunk000Sub001Block002 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block002Head surrogateDiagTailX0RatChunk000Sub001Block002Mid surrogateDiagTailX0RatChunk000Sub001Block002Tail surrogateDiagTailX0RatChunk000Sub001Block002
  ring

def SurrogateDiagonalTailChunk000Sub001Block002HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block002HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block002Head

def SurrogateDiagonalTailChunk000Sub001Block002MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block002MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block002Mid

def SurrogateDiagonalTailChunk000Sub001Block002TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block002TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block002Tail

theorem surrogateDiagonalTailChunk000Sub001Block002_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block002HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block002MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block002TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block002Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block002 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block002HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block002MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block002TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block002Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block002_eq_head_add_mid_add_tail

/-- Block 003 covers tail-support indices [5075,5100) and q from 8394 to 8437. -/

def TailChunk000Sub001Block003Part000SupportExplicit : Finset ℕ :=
  ([8394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part000 : ℚ :=
  (24450875 : ℚ) / 5092926660288

def SurrogateDiagonalTailChunk000Sub001Block003Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8394
    = surrogateDiagTailX0RatChunk000Sub001Block003Part000

theorem surrogateDiagonalTailChunk000Sub001Block003Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part000] using hcert

def TailChunk000Sub001Block003Part001SupportExplicit : Finset ℕ :=
  ([8395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part001 : ℚ :=
  (978185236975 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub001Block003Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8395
    = surrogateDiagTailX0RatChunk000Sub001Block003Part001

theorem surrogateDiagonalTailChunk000Sub001Block003Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part001] using hcert

def TailChunk000Sub001Block003Part002SupportExplicit : Finset ℕ :=
  ([8398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part002 : ℚ :=
  (157096911325 : ℚ) / 59452557788971008

def SurrogateDiagonalTailChunk000Sub001Block003Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8398
    = surrogateDiagTailX0RatChunk000Sub001Block003Part002

theorem surrogateDiagonalTailChunk000Sub001Block003Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part002] using hcert

def TailChunk000Sub001Block003Part003SupportExplicit : Finset ℕ :=
  ([8399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part003 : ℚ :=
  (3659763625 : ℚ) / 9510823877938704

def SurrogateDiagonalTailChunk000Sub001Block003Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8399
    = surrogateDiagTailX0RatChunk000Sub001Block003Part003

theorem surrogateDiagonalTailChunk000Sub001Block003Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part003] using hcert

def TailChunk000Sub001Block003Part004SupportExplicit : Finset ℕ :=
  ([8401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part004 : ℚ :=
  (167522565517 : ℚ) / 430553303442000000

def SurrogateDiagonalTailChunk000Sub001Block003Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8401
    = surrogateDiagTailX0RatChunk000Sub001Block003Part004

theorem surrogateDiagonalTailChunk000Sub001Block003Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part004] using hcert

def TailChunk000Sub001Block003Part005SupportExplicit : Finset ℕ :=
  ([8402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part005 : ℚ :=
  (17648401 : ℚ) / 12449273356800

def SurrogateDiagonalTailChunk000Sub001Block003Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8402
    = surrogateDiagTailX0RatChunk000Sub001Block003Part005

theorem surrogateDiagonalTailChunk000Sub001Block003Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part005] using hcert

def TailChunk000Sub001Block003Part006SupportExplicit : Finset ℕ :=
  ([8403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part006 : ℚ :=
  (49020337349 : ℚ) / 49182314496000000

def SurrogateDiagonalTailChunk000Sub001Block003Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8403
    = surrogateDiagTailX0RatChunk000Sub001Block003Part006

theorem surrogateDiagonalTailChunk000Sub001Block003Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part006] using hcert

def TailChunk000Sub001Block003Part007SupportExplicit : Finset ℕ :=
  ([8407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part007 : ℚ :=
  (7805359631 : ℚ) / 14932905984000000

def SurrogateDiagonalTailChunk000Sub001Block003Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8407
    = surrogateDiagTailX0RatChunk000Sub001Block003Part007

theorem surrogateDiagonalTailChunk000Sub001Block003Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part007] using hcert

def TailChunk000Sub001Block003Part008SupportExplicit : Finset ℕ :=
  ([8409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part008 : ℚ :=
  (76703708675 : ℚ) / 77067165663082404

def SurrogateDiagonalTailChunk000Sub001Block003Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8409
    = surrogateDiagTailX0RatChunk000Sub001Block003Part008

theorem surrogateDiagonalTailChunk000Sub001Block003Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part008] using hcert

def TailChunk000Sub001Block003Part009SupportExplicit : Finset ℕ :=
  ([8411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part009 : ℚ :=
  (657136958875 : ℚ) / 1504979778684423168

def SurrogateDiagonalTailChunk000Sub001Block003Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8411
    = surrogateDiagTailX0RatChunk000Sub001Block003Part009

theorem surrogateDiagonalTailChunk000Sub001Block003Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part009] using hcert

def TailChunk000Sub001Block003Part010SupportExplicit : Finset ℕ :=
  ([8413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part010 : ℚ :=
  (30859214625 : ℚ) / 81444002476399936

def SurrogateDiagonalTailChunk000Sub001Block003Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8413
    = surrogateDiagTailX0RatChunk000Sub001Block003Part010

theorem surrogateDiagonalTailChunk000Sub001Block003Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part010] using hcert

def TailChunk000Sub001Block003Part011SupportExplicit : Finset ℕ :=
  ([8414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part011 : ℚ :=
  (17796122731 : ℚ) / 4199879808000000

def SurrogateDiagonalTailChunk000Sub001Block003Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8414
    = surrogateDiagTailX0RatChunk000Sub001Block003Part011

theorem surrogateDiagonalTailChunk000Sub001Block003Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part011] using hcert

def TailChunk000Sub001Block003Part012SupportExplicit : Finset ℕ :=
  ([8417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part012 : ℚ :=
  (46555194925 : ℚ) / 3339525023000390016

def SurrogateDiagonalTailChunk000Sub001Block003Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8417
    = surrogateDiagTailX0RatChunk000Sub001Block003Part012

theorem surrogateDiagonalTailChunk000Sub001Block003Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part012] using hcert

def TailChunk000Sub001Block003Part013SupportExplicit : Finset ℕ :=
  ([8418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part013 : ℚ :=
  (1170617263 : ℚ) / 202437663436800

def SurrogateDiagonalTailChunk000Sub001Block003Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8418
    = surrogateDiagTailX0RatChunk000Sub001Block003Part013

theorem surrogateDiagonalTailChunk000Sub001Block003Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part013] using hcert

def TailChunk000Sub001Block003Part014SupportExplicit : Finset ℕ :=
  ([8419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block003Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8419
    = surrogateDiagTailX0RatChunk000Sub001Block003Part014

theorem surrogateDiagonalTailChunk000Sub001Block003Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part014] using hcert

def TailChunk000Sub001Block003Part015SupportExplicit : Finset ℕ :=
  ([8421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part015 : ℚ :=
  (894508909 : ℚ) / 1966473216000000

def SurrogateDiagonalTailChunk000Sub001Block003Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8421
    = surrogateDiagTailX0RatChunk000Sub001Block003Part015

theorem surrogateDiagonalTailChunk000Sub001Block003Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part015] using hcert

def TailChunk000Sub001Block003Part016SupportExplicit : Finset ℕ :=
  ([8422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part016 : ℚ :=
  (443313025 : ℚ) / 314206549554162

def SurrogateDiagonalTailChunk000Sub001Block003Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8422
    = surrogateDiagTailX0RatChunk000Sub001Block003Part016

theorem surrogateDiagonalTailChunk000Sub001Block003Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part016] using hcert

def TailChunk000Sub001Block003Part017SupportExplicit : Finset ℕ :=
  ([8423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block003Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8423
    = surrogateDiagTailX0RatChunk000Sub001Block003Part017

theorem surrogateDiagonalTailChunk000Sub001Block003Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part017] using hcert

def TailChunk000Sub001Block003Part018SupportExplicit : Finset ℕ :=
  ([8426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part018 : ℚ :=
  (40991455261 : ℚ) / 21298072538755200

def SurrogateDiagonalTailChunk000Sub001Block003Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8426
    = surrogateDiagTailX0RatChunk000Sub001Block003Part018

theorem surrogateDiagonalTailChunk000Sub001Block003Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part018] using hcert

def TailChunk000Sub001Block003Part019SupportExplicit : Finset ℕ :=
  ([8429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block003Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8429
    = surrogateDiagTailX0RatChunk000Sub001Block003Part019

theorem surrogateDiagonalTailChunk000Sub001Block003Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part019] using hcert

def TailChunk000Sub001Block003Part020SupportExplicit : Finset ℕ :=
  ([8430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part020 : ℚ :=
  (4623371103 : ℚ) / 419689083699200

def SurrogateDiagonalTailChunk000Sub001Block003Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8430
    = surrogateDiagTailX0RatChunk000Sub001Block003Part020

theorem surrogateDiagonalTailChunk000Sub001Block003Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part020] using hcert

def TailChunk000Sub001Block003Part021SupportExplicit : Finset ℕ :=
  ([8431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block003Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8431
    = surrogateDiagTailX0RatChunk000Sub001Block003Part021

theorem surrogateDiagonalTailChunk000Sub001Block003Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part021] using hcert

def TailChunk000Sub001Block003Part022SupportExplicit : Finset ℕ :=
  ([8434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part022 : ℚ :=
  (277860765625 : ℚ) / 197500989748449792

def SurrogateDiagonalTailChunk000Sub001Block003Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8434
    = surrogateDiagTailX0RatChunk000Sub001Block003Part022

theorem surrogateDiagonalTailChunk000Sub001Block003Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part022] using hcert

def TailChunk000Sub001Block003Part023SupportExplicit : Finset ℕ :=
  ([8435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part023 : ℚ :=
  (7307845087 : ℚ) / 27524332309708800

def SurrogateDiagonalTailChunk000Sub001Block003Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8435
    = surrogateDiagTailX0RatChunk000Sub001Block003Part023

theorem surrogateDiagonalTailChunk000Sub001Block003Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part023] using hcert

def TailChunk000Sub001Block003Part024SupportExplicit : Finset ℕ :=
  ([8437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part024 : ℚ :=
  (17278876273 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk000Sub001Block003Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8437
    = surrogateDiagTailX0RatChunk000Sub001Block003Part024

theorem surrogateDiagonalTailChunk000Sub001Block003Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block003HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block003Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block003Part000
    + surrogateDiagTailX0RatChunk000Sub001Block003Part001
    + surrogateDiagTailX0RatChunk000Sub001Block003Part002
    + surrogateDiagTailX0RatChunk000Sub001Block003Part003
    + surrogateDiagTailX0RatChunk000Sub001Block003Part004
    + surrogateDiagTailX0RatChunk000Sub001Block003Part005
    + surrogateDiagTailX0RatChunk000Sub001Block003Part006
    + surrogateDiagTailX0RatChunk000Sub001Block003Part007
    + surrogateDiagTailX0RatChunk000Sub001Block003Part008
    + surrogateDiagTailX0RatChunk000Sub001Block003Part009

def surrogateDiagonalTailChunk000Sub001Block003MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block003Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block003Part010
    + surrogateDiagTailX0RatChunk000Sub001Block003Part011
    + surrogateDiagTailX0RatChunk000Sub001Block003Part012
    + surrogateDiagTailX0RatChunk000Sub001Block003Part013
    + surrogateDiagTailX0RatChunk000Sub001Block003Part014
    + surrogateDiagTailX0RatChunk000Sub001Block003Part015
    + surrogateDiagTailX0RatChunk000Sub001Block003Part016
    + surrogateDiagTailX0RatChunk000Sub001Block003Part017
    + surrogateDiagTailX0RatChunk000Sub001Block003Part018
    + surrogateDiagTailX0RatChunk000Sub001Block003Part019

def surrogateDiagonalTailChunk000Sub001Block003TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block003Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block003Part020
    + surrogateDiagTailX0RatChunk000Sub001Block003Part021
    + surrogateDiagTailX0RatChunk000Sub001Block003Part022
    + surrogateDiagTailX0RatChunk000Sub001Block003Part023
    + surrogateDiagTailX0RatChunk000Sub001Block003Part024

def surrogateDiagonalTailChunk000Sub001Block003Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block003HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block003MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block003TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block003 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block003Part000
    + surrogateDiagTailX0RatChunk000Sub001Block003Part001
    + surrogateDiagTailX0RatChunk000Sub001Block003Part002
    + surrogateDiagTailX0RatChunk000Sub001Block003Part003
    + surrogateDiagTailX0RatChunk000Sub001Block003Part004
    + surrogateDiagTailX0RatChunk000Sub001Block003Part005
    + surrogateDiagTailX0RatChunk000Sub001Block003Part006
    + surrogateDiagTailX0RatChunk000Sub001Block003Part007
    + surrogateDiagTailX0RatChunk000Sub001Block003Part008
    + surrogateDiagTailX0RatChunk000Sub001Block003Part009
    + surrogateDiagTailX0RatChunk000Sub001Block003Part010
    + surrogateDiagTailX0RatChunk000Sub001Block003Part011
    + surrogateDiagTailX0RatChunk000Sub001Block003Part012
    + surrogateDiagTailX0RatChunk000Sub001Block003Part013
    + surrogateDiagTailX0RatChunk000Sub001Block003Part014
    + surrogateDiagTailX0RatChunk000Sub001Block003Part015
    + surrogateDiagTailX0RatChunk000Sub001Block003Part016
    + surrogateDiagTailX0RatChunk000Sub001Block003Part017
    + surrogateDiagTailX0RatChunk000Sub001Block003Part018
    + surrogateDiagTailX0RatChunk000Sub001Block003Part019
    + surrogateDiagTailX0RatChunk000Sub001Block003Part020
    + surrogateDiagTailX0RatChunk000Sub001Block003Part021
    + surrogateDiagTailX0RatChunk000Sub001Block003Part022
    + surrogateDiagTailX0RatChunk000Sub001Block003Part023
    + surrogateDiagTailX0RatChunk000Sub001Block003Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block003_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block003Head + surrogateDiagTailX0RatChunk000Sub001Block003Mid + surrogateDiagTailX0RatChunk000Sub001Block003Tail =
      surrogateDiagTailX0RatChunk000Sub001Block003 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block003Head surrogateDiagTailX0RatChunk000Sub001Block003Mid surrogateDiagTailX0RatChunk000Sub001Block003Tail surrogateDiagTailX0RatChunk000Sub001Block003
  ring

def SurrogateDiagonalTailChunk000Sub001Block003HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block003HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block003Head

def SurrogateDiagonalTailChunk000Sub001Block003MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block003MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block003Mid

def SurrogateDiagonalTailChunk000Sub001Block003TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block003TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block003Tail

theorem surrogateDiagonalTailChunk000Sub001Block003_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block003HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block003MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block003TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block003Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block003 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block003HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block003MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block003TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block003Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block003_eq_head_add_mid_add_tail

/-- Block 004 covers tail-support indices [5100,5125) and q from 8438 to 8481. -/

def TailChunk000Sub001Block004Part000SupportExplicit : Finset ℕ :=
  ([8438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part000 : ℚ :=
  (278124390625 : ℚ) / 197876021192390322

def SurrogateDiagonalTailChunk000Sub001Block004Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8438
    = surrogateDiagTailX0RatChunk000Sub001Block004Part000

theorem surrogateDiagonalTailChunk000Sub001Block004Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part000] using hcert

def TailChunk000Sub001Block004Part001SupportExplicit : Finset ℕ :=
  ([8439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part001 : ℚ :=
  (978467980075 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk000Sub001Block004Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8439
    = surrogateDiagTailX0RatChunk000Sub001Block004Part001

theorem surrogateDiagonalTailChunk000Sub001Block004Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part001] using hcert

def TailChunk000Sub001Block004Part002SupportExplicit : Finset ℕ :=
  ([8441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part002 : ℚ :=
  (123769984975 : ℚ) / 10510948876340423808

def SurrogateDiagonalTailChunk000Sub001Block004Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8441
    = surrogateDiagTailX0RatChunk000Sub001Block004Part002

theorem surrogateDiagonalTailChunk000Sub001Block004Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part002] using hcert

def TailChunk000Sub001Block004Part003SupportExplicit : Finset ℕ :=
  ([8443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block004Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8443
    = surrogateDiagTailX0RatChunk000Sub001Block004Part003

theorem surrogateDiagonalTailChunk000Sub001Block004Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part003] using hcert

def TailChunk000Sub001Block004Part004SupportExplicit : Finset ℕ :=
  ([8445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part004 : ℚ :=
  (290330046075 : ℚ) / 340573470114021376

def SurrogateDiagonalTailChunk000Sub001Block004Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8445
    = surrogateDiagTailX0RatChunk000Sub001Block004Part004

theorem surrogateDiagonalTailChunk000Sub001Block004Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part004] using hcert

def TailChunk000Sub001Block004Part005SupportExplicit : Finset ℕ :=
  ([8446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part005 : ℚ :=
  (10835739067 : ℚ) / 6928951337164800

def SurrogateDiagonalTailChunk000Sub001Block004Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8446
    = surrogateDiagTailX0RatChunk000Sub001Block004Part005

theorem surrogateDiagonalTailChunk000Sub001Block004Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part005] using hcert

def TailChunk000Sub001Block004Part006SupportExplicit : Finset ℕ :=
  ([8447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block004Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8447
    = surrogateDiagTailX0RatChunk000Sub001Block004Part006

theorem surrogateDiagonalTailChunk000Sub001Block004Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part006] using hcert

def TailChunk000Sub001Block004Part007SupportExplicit : Finset ℕ :=
  ([8449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part007 : ℚ :=
  (537943583 : ℚ) / 5827682705080320

def SurrogateDiagonalTailChunk000Sub001Block004Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8449
    = surrogateDiagTailX0RatChunk000Sub001Block004Part007

theorem surrogateDiagonalTailChunk000Sub001Block004Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part007] using hcert

def TailChunk000Sub001Block004Part008SupportExplicit : Finset ℕ :=
  ([8453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part008 : ℚ :=
  (56965515625 : ℚ) / 11685000376046095488

def SurrogateDiagonalTailChunk000Sub001Block004Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8453
    = surrogateDiagTailX0RatChunk000Sub001Block004Part008

theorem surrogateDiagonalTailChunk000Sub001Block004Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part008] using hcert

def TailChunk000Sub001Block004Part009SupportExplicit : Finset ℕ :=
  ([8454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part009 : ℚ :=
  (868101462025 : ℚ) / 157237981759930368

def SurrogateDiagonalTailChunk000Sub001Block004Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8454
    = surrogateDiagTailX0RatChunk000Sub001Block004Part009

theorem surrogateDiagonalTailChunk000Sub001Block004Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part009] using hcert

def TailChunk000Sub001Block004Part010SupportExplicit : Finset ℕ :=
  ([8455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part010 : ℚ :=
  (598503765775 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk000Sub001Block004Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8455
    = surrogateDiagTailX0RatChunk000Sub001Block004Part010

theorem surrogateDiagonalTailChunk000Sub001Block004Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part010] using hcert

def TailChunk000Sub001Block004Part011SupportExplicit : Finset ℕ :=
  ([8457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part011 : ℚ :=
  (496533407525 : ℚ) / 1261481253469053504

def SurrogateDiagonalTailChunk000Sub001Block004Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8457
    = surrogateDiagTailX0RatChunk000Sub001Block004Part011

theorem surrogateDiagonalTailChunk000Sub001Block004Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part011] using hcert

def TailChunk000Sub001Block004Part012SupportExplicit : Finset ℕ :=
  ([8458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part012 : ℚ :=
  (279444390625 : ℚ) / 199759196330656032

def SurrogateDiagonalTailChunk000Sub001Block004Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8458
    = surrogateDiagTailX0RatChunk000Sub001Block004Part012

theorem surrogateDiagonalTailChunk000Sub001Block004Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part012] using hcert

def TailChunk000Sub001Block004Part013SupportExplicit : Finset ℕ :=
  ([8459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part013 : ℚ :=
  (896359153 : ℚ) / 34796192944619520

def SurrogateDiagonalTailChunk000Sub001Block004Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8459
    = surrogateDiagTailX0RatChunk000Sub001Block004Part013

theorem surrogateDiagonalTailChunk000Sub001Block004Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part013] using hcert

def TailChunk000Sub001Block004Part014SupportExplicit : Finset ℕ :=
  ([8461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block004Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8461
    = surrogateDiagTailX0RatChunk000Sub001Block004Part014

theorem surrogateDiagonalTailChunk000Sub001Block004Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part014] using hcert

def TailChunk000Sub001Block004Part015SupportExplicit : Finset ℕ :=
  ([8462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part015 : ℚ :=
  (447534025 : ℚ) / 320219901584082

def SurrogateDiagonalTailChunk000Sub001Block004Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8462
    = surrogateDiagTailX0RatChunk000Sub001Block004Part015

theorem surrogateDiagonalTailChunk000Sub001Block004Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part015] using hcert

def TailChunk000Sub001Block004Part016SupportExplicit : Finset ℕ :=
  ([8463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part016 : ℚ :=
  (7300878083 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk000Sub001Block004Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8463
    = surrogateDiagTailX0RatChunk000Sub001Block004Part016

theorem surrogateDiagonalTailChunk000Sub001Block004Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part016] using hcert

def TailChunk000Sub001Block004Part017SupportExplicit : Finset ℕ :=
  ([8465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part017 : ℚ :=
  (268911229475 : ℚ) / 2623241433776799744

def SurrogateDiagonalTailChunk000Sub001Block004Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8465
    = surrogateDiagTailX0RatChunk000Sub001Block004Part017

theorem surrogateDiagonalTailChunk000Sub001Block004Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part017] using hcert

def TailChunk000Sub001Block004Part018SupportExplicit : Finset ℕ :=
  ([8466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part018 : ℚ :=
  (70330575 : ℚ) / 11852100665344

def SurrogateDiagonalTailChunk000Sub001Block004Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8466
    = surrogateDiagTailX0RatChunk000Sub001Block004Part018

theorem surrogateDiagonalTailChunk000Sub001Block004Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part018] using hcert

def TailChunk000Sub001Block004Part019SupportExplicit : Finset ℕ :=
  ([8467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block004Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8467
    = surrogateDiagTailX0RatChunk000Sub001Block004Part019

theorem surrogateDiagonalTailChunk000Sub001Block004Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part019] using hcert

def TailChunk000Sub001Block004Part020SupportExplicit : Finset ℕ :=
  ([8471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part020 : ℚ :=
  (72935682775 : ℚ) / 11482813359448639488

def SurrogateDiagonalTailChunk000Sub001Block004Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8471
    = surrogateDiagTailX0RatChunk000Sub001Block004Part020

theorem surrogateDiagonalTailChunk000Sub001Block004Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part020] using hcert

def TailChunk000Sub001Block004Part021SupportExplicit : Finset ℕ :=
  ([8473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part021 : ℚ :=
  (2168836325 : ℚ) / 298670723052650496

def SurrogateDiagonalTailChunk000Sub001Block004Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8473
    = surrogateDiagTailX0RatChunk000Sub001Block004Part021

theorem surrogateDiagonalTailChunk000Sub001Block004Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part021] using hcert

def TailChunk000Sub001Block004Part022SupportExplicit : Finset ℕ :=
  ([8474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part022 : ℚ :=
  (33390459125 : ℚ) / 19924103944004004

def SurrogateDiagonalTailChunk000Sub001Block004Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8474
    = surrogateDiagTailX0RatChunk000Sub001Block004Part022

theorem surrogateDiagonalTailChunk000Sub001Block004Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part022] using hcert

def TailChunk000Sub001Block004Part023SupportExplicit : Finset ℕ :=
  ([8479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part023 : ℚ :=
  (9657349243 : ℚ) / 26117745896678400

def SurrogateDiagonalTailChunk000Sub001Block004Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8479
    = surrogateDiagTailX0RatChunk000Sub001Block004Part023

theorem surrogateDiagonalTailChunk000Sub001Block004Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part023] using hcert

def TailChunk000Sub001Block004Part024SupportExplicit : Finset ℕ :=
  ([8481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part024 : ℚ :=
  (87424788241 : ℚ) / 68733220631347200

def SurrogateDiagonalTailChunk000Sub001Block004Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8481
    = surrogateDiagTailX0RatChunk000Sub001Block004Part024

theorem surrogateDiagonalTailChunk000Sub001Block004Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block004HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block004Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block004Part000
    + surrogateDiagTailX0RatChunk000Sub001Block004Part001
    + surrogateDiagTailX0RatChunk000Sub001Block004Part002
    + surrogateDiagTailX0RatChunk000Sub001Block004Part003
    + surrogateDiagTailX0RatChunk000Sub001Block004Part004
    + surrogateDiagTailX0RatChunk000Sub001Block004Part005
    + surrogateDiagTailX0RatChunk000Sub001Block004Part006
    + surrogateDiagTailX0RatChunk000Sub001Block004Part007
    + surrogateDiagTailX0RatChunk000Sub001Block004Part008
    + surrogateDiagTailX0RatChunk000Sub001Block004Part009

def surrogateDiagonalTailChunk000Sub001Block004MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block004Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block004Part010
    + surrogateDiagTailX0RatChunk000Sub001Block004Part011
    + surrogateDiagTailX0RatChunk000Sub001Block004Part012
    + surrogateDiagTailX0RatChunk000Sub001Block004Part013
    + surrogateDiagTailX0RatChunk000Sub001Block004Part014
    + surrogateDiagTailX0RatChunk000Sub001Block004Part015
    + surrogateDiagTailX0RatChunk000Sub001Block004Part016
    + surrogateDiagTailX0RatChunk000Sub001Block004Part017
    + surrogateDiagTailX0RatChunk000Sub001Block004Part018
    + surrogateDiagTailX0RatChunk000Sub001Block004Part019

def surrogateDiagonalTailChunk000Sub001Block004TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block004Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block004Part020
    + surrogateDiagTailX0RatChunk000Sub001Block004Part021
    + surrogateDiagTailX0RatChunk000Sub001Block004Part022
    + surrogateDiagTailX0RatChunk000Sub001Block004Part023
    + surrogateDiagTailX0RatChunk000Sub001Block004Part024

def surrogateDiagonalTailChunk000Sub001Block004Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block004HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block004MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block004TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block004 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block004Part000
    + surrogateDiagTailX0RatChunk000Sub001Block004Part001
    + surrogateDiagTailX0RatChunk000Sub001Block004Part002
    + surrogateDiagTailX0RatChunk000Sub001Block004Part003
    + surrogateDiagTailX0RatChunk000Sub001Block004Part004
    + surrogateDiagTailX0RatChunk000Sub001Block004Part005
    + surrogateDiagTailX0RatChunk000Sub001Block004Part006
    + surrogateDiagTailX0RatChunk000Sub001Block004Part007
    + surrogateDiagTailX0RatChunk000Sub001Block004Part008
    + surrogateDiagTailX0RatChunk000Sub001Block004Part009
    + surrogateDiagTailX0RatChunk000Sub001Block004Part010
    + surrogateDiagTailX0RatChunk000Sub001Block004Part011
    + surrogateDiagTailX0RatChunk000Sub001Block004Part012
    + surrogateDiagTailX0RatChunk000Sub001Block004Part013
    + surrogateDiagTailX0RatChunk000Sub001Block004Part014
    + surrogateDiagTailX0RatChunk000Sub001Block004Part015
    + surrogateDiagTailX0RatChunk000Sub001Block004Part016
    + surrogateDiagTailX0RatChunk000Sub001Block004Part017
    + surrogateDiagTailX0RatChunk000Sub001Block004Part018
    + surrogateDiagTailX0RatChunk000Sub001Block004Part019
    + surrogateDiagTailX0RatChunk000Sub001Block004Part020
    + surrogateDiagTailX0RatChunk000Sub001Block004Part021
    + surrogateDiagTailX0RatChunk000Sub001Block004Part022
    + surrogateDiagTailX0RatChunk000Sub001Block004Part023
    + surrogateDiagTailX0RatChunk000Sub001Block004Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block004_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block004Head + surrogateDiagTailX0RatChunk000Sub001Block004Mid + surrogateDiagTailX0RatChunk000Sub001Block004Tail =
      surrogateDiagTailX0RatChunk000Sub001Block004 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block004Head surrogateDiagTailX0RatChunk000Sub001Block004Mid surrogateDiagTailX0RatChunk000Sub001Block004Tail surrogateDiagTailX0RatChunk000Sub001Block004
  ring

def SurrogateDiagonalTailChunk000Sub001Block004HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block004HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block004Head

def SurrogateDiagonalTailChunk000Sub001Block004MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block004MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block004Mid

def SurrogateDiagonalTailChunk000Sub001Block004TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block004TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block004Tail

theorem surrogateDiagonalTailChunk000Sub001Block004_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block004HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block004MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block004TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block004Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block004 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block004HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block004MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block004TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block004Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block004_eq_head_add_mid_add_tail

/-- Block 005 covers tail-support indices [5125,5150) and q from 8482 to 8518. -/

def TailChunk000Sub001Block005Part000SupportExplicit : Finset ℕ :=
  ([8482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part000 : ℚ :=
  (89912418919 : ℚ) / 32325874058035200

def SurrogateDiagonalTailChunk000Sub001Block005Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8482
    = surrogateDiagTailX0RatChunk000Sub001Block005Part000

theorem surrogateDiagonalTailChunk000Sub001Block005Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part000] using hcert

def TailChunk000Sub001Block005Part001SupportExplicit : Finset ℕ :=
  ([8483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part001 : ℚ :=
  (4113217609375 : ℚ) / 10079155849265676288

def SurrogateDiagonalTailChunk000Sub001Block005Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8483
    = surrogateDiagTailX0RatChunk000Sub001Block005Part001

theorem surrogateDiagonalTailChunk000Sub001Block005Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part001] using hcert

def TailChunk000Sub001Block005Part002SupportExplicit : Finset ℕ :=
  ([8485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part002 : ℚ :=
  (1079240555775 : ℚ) / 1765423735222829056

def SurrogateDiagonalTailChunk000Sub001Block005Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8485
    = surrogateDiagTailX0RatChunk000Sub001Block005Part002

theorem surrogateDiagonalTailChunk000Sub001Block005Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part002] using hcert

def TailChunk000Sub001Block005Part003SupportExplicit : Finset ℕ :=
  ([8486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part003 : ℚ :=
  (2249931048775 : ℚ) / 809672736042015048

def SurrogateDiagonalTailChunk000Sub001Block005Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8486
    = surrogateDiagTailX0RatChunk000Sub001Block005Part003

theorem surrogateDiagonalTailChunk000Sub001Block005Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part003] using hcert

def TailChunk000Sub001Block005Part004SupportExplicit : Finset ℕ :=
  ([8489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part004 : ℚ :=
  (167347219525 : ℚ) / 390419035556032512

def SurrogateDiagonalTailChunk000Sub001Block005Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8489
    = surrogateDiagTailX0RatChunk000Sub001Block005Part004

theorem surrogateDiagonalTailChunk000Sub001Block005Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part004] using hcert

def TailChunk000Sub001Block005Part005SupportExplicit : Finset ℕ :=
  ([8490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part005 : ℚ :=
  (157217374375 : ℚ) / 16192848356646912

def SurrogateDiagonalTailChunk000Sub001Block005Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8490
    = surrogateDiagTailX0RatChunk000Sub001Block005Part005

theorem surrogateDiagonalTailChunk000Sub001Block005Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part005] using hcert

def TailChunk000Sub001Block005Part006SupportExplicit : Finset ℕ :=
  ([8491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part006 : ℚ :=
  (199054093475 : ℚ) / 388481046197584896

def SurrogateDiagonalTailChunk000Sub001Block005Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8491
    = surrogateDiagTailX0RatChunk000Sub001Block005Part006

theorem surrogateDiagonalTailChunk000Sub001Block005Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part006] using hcert

def TailChunk000Sub001Block005Part007SupportExplicit : Finset ℕ :=
  ([8493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part007 : ℚ :=
  (385694996975 : ℚ) / 335840040142553088

def SurrogateDiagonalTailChunk000Sub001Block005Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8493
    = surrogateDiagTailX0RatChunk000Sub001Block005Part007

theorem surrogateDiagonalTailChunk000Sub001Block005Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part007] using hcert

def TailChunk000Sub001Block005Part008SupportExplicit : Finset ℕ :=
  ([8494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part008 : ℚ :=
  (21830525429 : ℚ) / 13857902674329600

def SurrogateDiagonalTailChunk000Sub001Block005Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8494
    = surrogateDiagTailX0RatChunk000Sub001Block005Part008

theorem surrogateDiagonalTailChunk000Sub001Block005Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part008] using hcert

def TailChunk000Sub001Block005Part009SupportExplicit : Finset ℕ :=
  ([8495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part009 : ℚ :=
  (3245359355425 : ℚ) / 5321297842353358848

def SurrogateDiagonalTailChunk000Sub001Block005Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8495
    = surrogateDiagTailX0RatChunk000Sub001Block005Part009

theorem surrogateDiagonalTailChunk000Sub001Block005Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part009] using hcert

def TailChunk000Sub001Block005Part010SupportExplicit : Finset ℕ :=
  ([8497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part010 : ℚ :=
  (305184179675 : ℚ) / 798109268568686592

def SurrogateDiagonalTailChunk000Sub001Block005Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8497
    = surrogateDiagTailX0RatChunk000Sub001Block005Part010

theorem surrogateDiagonalTailChunk000Sub001Block005Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part010] using hcert

def TailChunk000Sub001Block005Part011SupportExplicit : Finset ℕ :=
  ([8498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part011 : ℚ :=
  (247252925875 : ℚ) / 109260294243070752

def SurrogateDiagonalTailChunk000Sub001Block005Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8498
    = surrogateDiagTailX0RatChunk000Sub001Block005Part011

theorem surrogateDiagonalTailChunk000Sub001Block005Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part011] using hcert

def TailChunk000Sub001Block005Part012SupportExplicit : Finset ℕ :=
  ([8499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part012 : ℚ :=
  (1253672938925 : ℚ) / 1286737156175560704

def SurrogateDiagonalTailChunk000Sub001Block005Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8499
    = surrogateDiagTailX0RatChunk000Sub001Block005Part012

theorem surrogateDiagonalTailChunk000Sub001Block005Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part012] using hcert

def TailChunk000Sub001Block005Part013SupportExplicit : Finset ℕ :=
  ([8501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part013 : ℚ :=
  (72267001 : ℚ) / 208844260500000

def SurrogateDiagonalTailChunk000Sub001Block005Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8501
    = surrogateDiagTailX0RatChunk000Sub001Block005Part013

theorem surrogateDiagonalTailChunk000Sub001Block005Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part013] using hcert

def TailChunk000Sub001Block005Part014SupportExplicit : Finset ℕ :=
  ([8502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part014 : ℚ :=
  (401818774625 : ℚ) / 56433482588749824

def SurrogateDiagonalTailChunk000Sub001Block005Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8502
    = surrogateDiagTailX0RatChunk000Sub001Block005Part014

theorem surrogateDiagonalTailChunk000Sub001Block005Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part014] using hcert

def TailChunk000Sub001Block005Part015SupportExplicit : Finset ℕ :=
  ([8503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part015 : ℚ :=
  (3161749085 : ℚ) / 7105359352833024

def SurrogateDiagonalTailChunk000Sub001Block005Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8503
    = surrogateDiagTailX0RatChunk000Sub001Block005Part015

theorem surrogateDiagonalTailChunk000Sub001Block005Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part015] using hcert

def TailChunk000Sub001Block005Part016SupportExplicit : Finset ℕ :=
  ([8506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part016 : ℚ :=
  (282625140625 : ℚ) / 204333649111870752

def SurrogateDiagonalTailChunk000Sub001Block005Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8506
    = surrogateDiagTailX0RatChunk000Sub001Block005Part016

theorem surrogateDiagonalTailChunk000Sub001Block005Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part016] using hcert

def TailChunk000Sub001Block005Part017SupportExplicit : Finset ℕ :=
  ([8507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part017 : ℚ :=
  (87089735621 : ℚ) / 235059713070105600

def SurrogateDiagonalTailChunk000Sub001Block005Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8507
    = surrogateDiagTailX0RatChunk000Sub001Block005Part017

theorem surrogateDiagonalTailChunk000Sub001Block005Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part017] using hcert

def TailChunk000Sub001Block005Part018SupportExplicit : Finset ℕ :=
  ([8509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part018 : ℚ :=
  (14224411175 : ℚ) / 38827020499809696

def SurrogateDiagonalTailChunk000Sub001Block005Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8509
    = surrogateDiagTailX0RatChunk000Sub001Block005Part018

theorem surrogateDiagonalTailChunk000Sub001Block005Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part018] using hcert

def TailChunk000Sub001Block005Part019SupportExplicit : Finset ℕ :=
  ([8510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part019 : ℚ :=
  (446274368975 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub001Block005Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8510
    = surrogateDiagTailX0RatChunk000Sub001Block005Part019

theorem surrogateDiagonalTailChunk000Sub001Block005Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part019] using hcert

def TailChunk000Sub001Block005Part020SupportExplicit : Finset ℕ :=
  ([8511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part020 : ℚ :=
  (1257216005675 : ℚ) / 1294022274040587264

def SurrogateDiagonalTailChunk000Sub001Block005Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8511
    = surrogateDiagTailX0RatChunk000Sub001Block005Part020

theorem surrogateDiagonalTailChunk000Sub001Block005Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part020] using hcert

def TailChunk000Sub001Block005Part021SupportExplicit : Finset ℕ :=
  ([8513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part021 : ℚ :=
  (1132362015625 : ℚ) / 3281658064605806592

def SurrogateDiagonalTailChunk000Sub001Block005Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8513
    = surrogateDiagTailX0RatChunk000Sub001Block005Part021

theorem surrogateDiagonalTailChunk000Sub001Block005Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part021] using hcert

def TailChunk000Sub001Block005Part022SupportExplicit : Finset ℕ :=
  ([8515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part022 : ℚ :=
  (23080578701 : ℚ) / 30328798421975040

def SurrogateDiagonalTailChunk000Sub001Block005Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8515
    = surrogateDiagTailX0RatChunk000Sub001Block005Part022

theorem surrogateDiagonalTailChunk000Sub001Block005Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part022] using hcert

def TailChunk000Sub001Block005Part023SupportExplicit : Finset ℕ :=
  ([8517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part023 : ℚ :=
  (620996979075 : ℚ) / 663648121762349056

def SurrogateDiagonalTailChunk000Sub001Block005Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8517
    = surrogateDiagTailX0RatChunk000Sub001Block005Part023

theorem surrogateDiagonalTailChunk000Sub001Block005Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part023] using hcert

def TailChunk000Sub001Block005Part024SupportExplicit : Finset ℕ :=
  ([8518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part024 : ℚ :=
  (283423140625 : ℚ) / 205489434017679762

def SurrogateDiagonalTailChunk000Sub001Block005Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8518
    = surrogateDiagTailX0RatChunk000Sub001Block005Part024

theorem surrogateDiagonalTailChunk000Sub001Block005Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block005HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block005Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block005Part000
    + surrogateDiagTailX0RatChunk000Sub001Block005Part001
    + surrogateDiagTailX0RatChunk000Sub001Block005Part002
    + surrogateDiagTailX0RatChunk000Sub001Block005Part003
    + surrogateDiagTailX0RatChunk000Sub001Block005Part004
    + surrogateDiagTailX0RatChunk000Sub001Block005Part005
    + surrogateDiagTailX0RatChunk000Sub001Block005Part006
    + surrogateDiagTailX0RatChunk000Sub001Block005Part007
    + surrogateDiagTailX0RatChunk000Sub001Block005Part008
    + surrogateDiagTailX0RatChunk000Sub001Block005Part009

def surrogateDiagonalTailChunk000Sub001Block005MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block005Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block005Part010
    + surrogateDiagTailX0RatChunk000Sub001Block005Part011
    + surrogateDiagTailX0RatChunk000Sub001Block005Part012
    + surrogateDiagTailX0RatChunk000Sub001Block005Part013
    + surrogateDiagTailX0RatChunk000Sub001Block005Part014
    + surrogateDiagTailX0RatChunk000Sub001Block005Part015
    + surrogateDiagTailX0RatChunk000Sub001Block005Part016
    + surrogateDiagTailX0RatChunk000Sub001Block005Part017
    + surrogateDiagTailX0RatChunk000Sub001Block005Part018
    + surrogateDiagTailX0RatChunk000Sub001Block005Part019

def surrogateDiagonalTailChunk000Sub001Block005TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block005Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block005Part020
    + surrogateDiagTailX0RatChunk000Sub001Block005Part021
    + surrogateDiagTailX0RatChunk000Sub001Block005Part022
    + surrogateDiagTailX0RatChunk000Sub001Block005Part023
    + surrogateDiagTailX0RatChunk000Sub001Block005Part024

def surrogateDiagonalTailChunk000Sub001Block005Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block005HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block005MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block005TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block005 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block005Part000
    + surrogateDiagTailX0RatChunk000Sub001Block005Part001
    + surrogateDiagTailX0RatChunk000Sub001Block005Part002
    + surrogateDiagTailX0RatChunk000Sub001Block005Part003
    + surrogateDiagTailX0RatChunk000Sub001Block005Part004
    + surrogateDiagTailX0RatChunk000Sub001Block005Part005
    + surrogateDiagTailX0RatChunk000Sub001Block005Part006
    + surrogateDiagTailX0RatChunk000Sub001Block005Part007
    + surrogateDiagTailX0RatChunk000Sub001Block005Part008
    + surrogateDiagTailX0RatChunk000Sub001Block005Part009
    + surrogateDiagTailX0RatChunk000Sub001Block005Part010
    + surrogateDiagTailX0RatChunk000Sub001Block005Part011
    + surrogateDiagTailX0RatChunk000Sub001Block005Part012
    + surrogateDiagTailX0RatChunk000Sub001Block005Part013
    + surrogateDiagTailX0RatChunk000Sub001Block005Part014
    + surrogateDiagTailX0RatChunk000Sub001Block005Part015
    + surrogateDiagTailX0RatChunk000Sub001Block005Part016
    + surrogateDiagTailX0RatChunk000Sub001Block005Part017
    + surrogateDiagTailX0RatChunk000Sub001Block005Part018
    + surrogateDiagTailX0RatChunk000Sub001Block005Part019
    + surrogateDiagTailX0RatChunk000Sub001Block005Part020
    + surrogateDiagTailX0RatChunk000Sub001Block005Part021
    + surrogateDiagTailX0RatChunk000Sub001Block005Part022
    + surrogateDiagTailX0RatChunk000Sub001Block005Part023
    + surrogateDiagTailX0RatChunk000Sub001Block005Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block005_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block005Head + surrogateDiagTailX0RatChunk000Sub001Block005Mid + surrogateDiagTailX0RatChunk000Sub001Block005Tail =
      surrogateDiagTailX0RatChunk000Sub001Block005 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block005Head surrogateDiagTailX0RatChunk000Sub001Block005Mid surrogateDiagTailX0RatChunk000Sub001Block005Tail surrogateDiagTailX0RatChunk000Sub001Block005
  ring

def SurrogateDiagonalTailChunk000Sub001Block005HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block005HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block005Head

def SurrogateDiagonalTailChunk000Sub001Block005MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block005MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block005Mid

def SurrogateDiagonalTailChunk000Sub001Block005TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block005TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block005Tail

theorem surrogateDiagonalTailChunk000Sub001Block005_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block005HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block005MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block005TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block005Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block005 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block005HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block005MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block005TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block005Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block005_eq_head_add_mid_add_tail

/-- Block 006 covers tail-support indices [5150,5175) and q from 8519 to 8558. -/

def TailChunk000Sub001Block006Part000SupportExplicit : Finset ℕ :=
  ([8519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part000 : ℚ :=
  (200369462375 : ℚ) / 393634953188868096

def SurrogateDiagonalTailChunk000Sub001Block006Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8519
    = surrogateDiagTailX0RatChunk000Sub001Block006Part000

theorem surrogateDiagonalTailChunk000Sub001Block006Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part000] using hcert

def TailChunk000Sub001Block006Part001SupportExplicit : Finset ℕ :=
  ([8521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part001 : ℚ :=
  (1815186025 : ℚ) / 5270420045394432

def SurrogateDiagonalTailChunk000Sub001Block006Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8521
    = surrogateDiagTailX0RatChunk000Sub001Block006Part001

theorem surrogateDiagonalTailChunk000Sub001Block006Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part001] using hcert

def TailChunk000Sub001Block006Part002SupportExplicit : Finset ℕ :=
  ([8522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part002 : ℚ :=
  (453903025 : ℚ) / 329401252837152

def SurrogateDiagonalTailChunk000Sub001Block006Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8522
    = surrogateDiagTailX0RatChunk000Sub001Block006Part002

theorem surrogateDiagonalTailChunk000Sub001Block006Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part002] using hcert

def TailChunk000Sub001Block006Part003SupportExplicit : Finset ℕ :=
  ([8527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part003 : ℚ :=
  (1136089515625 : ℚ) / 3303301243168615122

def SurrogateDiagonalTailChunk000Sub001Block006Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8527
    = surrogateDiagTailX0RatChunk000Sub001Block006Part003

theorem surrogateDiagonalTailChunk000Sub001Block006Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part003] using hcert

def TailChunk000Sub001Block006Part004SupportExplicit : Finset ℕ :=
  ([8529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part004 : ℚ :=
  (315634995575 : ℚ) / 326251974633937296

def SurrogateDiagonalTailChunk000Sub001Block006Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8529
    = surrogateDiagTailX0RatChunk000Sub001Block006Part004

theorem surrogateDiagonalTailChunk000Sub001Block006Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part004] using hcert

def TailChunk000Sub001Block006Part005SupportExplicit : Finset ℕ :=
  ([8530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part005 : ℚ :=
  (954180306625 : ℚ) / 337306882905243648

def SurrogateDiagonalTailChunk000Sub001Block006Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8530
    = surrogateDiagTailX0RatChunk000Sub001Block006Part005

theorem surrogateDiagonalTailChunk000Sub001Block006Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part005] using hcert

def TailChunk000Sub001Block006Part006SupportExplicit : Finset ℕ :=
  ([8531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part006 : ℚ :=
  (16390525075 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub001Block006Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8531
    = surrogateDiagTailX0RatChunk000Sub001Block006Part006

theorem surrogateDiagonalTailChunk000Sub001Block006Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part006] using hcert

def TailChunk000Sub001Block006Part007SupportExplicit : Finset ℕ :=
  ([8533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part007 : ℚ :=
  (369199384025 : ℚ) / 616727691244634112

def SurrogateDiagonalTailChunk000Sub001Block006Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8533
    = surrogateDiagTailX0RatChunk000Sub001Block006Part007

theorem surrogateDiagonalTailChunk000Sub001Block006Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part007] using hcert

def TailChunk000Sub001Block006Part008SupportExplicit : Finset ℕ :=
  ([8534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part008 : ℚ :=
  (10755055087 : ℚ) / 6401280000000000

def SurrogateDiagonalTailChunk000Sub001Block006Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8534
    = surrogateDiagTailX0RatChunk000Sub001Block006Part008

theorem surrogateDiagonalTailChunk000Sub001Block006Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part008] using hcert

def TailChunk000Sub001Block006Part009SupportExplicit : Finset ℕ :=
  ([8535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part009 : ℚ :=
  (939009986975 : ℚ) / 533028160640385024

def SurrogateDiagonalTailChunk000Sub001Block006Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8535
    = surrogateDiagTailX0RatChunk000Sub001Block006Part009

theorem surrogateDiagonalTailChunk000Sub001Block006Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part009] using hcert

def TailChunk000Sub001Block006Part010SupportExplicit : Finset ℕ :=
  ([8537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part010 : ℚ :=
  (1138755765625 : ℚ) / 3318826072477757952

def SurrogateDiagonalTailChunk000Sub001Block006Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8537
    = surrogateDiagTailX0RatChunk000Sub001Block006Part010

theorem surrogateDiagonalTailChunk000Sub001Block006Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part010] using hcert

def TailChunk000Sub001Block006Part011SupportExplicit : Finset ℕ :=
  ([8538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part011 : ℚ :=
  (25296875 : ℚ) / 5451764937408

def SurrogateDiagonalTailChunk000Sub001Block006Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8538
    = surrogateDiagTailX0RatChunk000Sub001Block006Part011

theorem surrogateDiagonalTailChunk000Sub001Block006Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part011] using hcert

def TailChunk000Sub001Block006Part012SupportExplicit : Finset ℕ :=
  ([8539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part012 : ℚ :=
  (1139289390625 : ℚ) / 3321937593250926642

def SurrogateDiagonalTailChunk000Sub001Block006Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8539
    = surrogateDiagTailX0RatChunk000Sub001Block006Part012

theorem surrogateDiagonalTailChunk000Sub001Block006Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part012] using hcert

def TailChunk000Sub001Block006Part013SupportExplicit : Finset ℕ :=
  ([8542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part013 : ℚ :=
  (456036025 : ℚ) / 332505130138482

def SurrogateDiagonalTailChunk000Sub001Block006Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8542
    = surrogateDiagTailX0RatChunk000Sub001Block006Part013

theorem surrogateDiagonalTailChunk000Sub001Block006Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part013] using hcert

def TailChunk000Sub001Block006Part014SupportExplicit : Finset ℕ :=
  ([8543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part014 : ℚ :=
  (1140357015625 : ℚ) / 3328167197904322962

def SurrogateDiagonalTailChunk000Sub001Block006Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8543
    = surrogateDiagTailX0RatChunk000Sub001Block006Part014

theorem surrogateDiagonalTailChunk000Sub001Block006Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part014] using hcert

def TailChunk000Sub001Block006Part015SupportExplicit : Finset ℕ :=
  ([8545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part015 : ℚ :=
  (156365848425 : ℚ) / 259417335818518528

def SurrogateDiagonalTailChunk000Sub001Block006Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8545
    = surrogateDiagTailX0RatChunk000Sub001Block006Part015

theorem surrogateDiagonalTailChunk000Sub001Block006Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part015] using hcert

def TailChunk000Sub001Block006Part016SupportExplicit : Finset ℕ :=
  ([8546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part016 : ℚ :=
  (285289515625 : ℚ) / 208205330239660032

def SurrogateDiagonalTailChunk000Sub001Block006Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8546
    = surrogateDiagTailX0RatChunk000Sub001Block006Part016

theorem surrogateDiagonalTailChunk000Sub001Block006Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part016] using hcert

def TailChunk000Sub001Block006Part017SupportExplicit : Finset ℕ :=
  ([8547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part017 : ℚ :=
  (1466006977 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub001Block006Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8547
    = surrogateDiagTailX0RatChunk000Sub001Block006Part017

theorem surrogateDiagonalTailChunk000Sub001Block006Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part017] using hcert

def TailChunk000Sub001Block006Part018SupportExplicit : Finset ℕ :=
  ([8549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part018 : ℚ :=
  (4428664615225 : ℚ) / 12237225287161339008

def SurrogateDiagonalTailChunk000Sub001Block006Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8549
    = surrogateDiagTailX0RatChunk000Sub001Block006Part018

theorem surrogateDiagonalTailChunk000Sub001Block006Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part018] using hcert

def TailChunk000Sub001Block006Part019SupportExplicit : Finset ℕ :=
  ([8551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part019 : ℚ :=
  (4163677587925 : ℚ) / 10406906629194252288

def SurrogateDiagonalTailChunk000Sub001Block006Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8551
    = surrogateDiagTailX0RatChunk000Sub001Block006Part019

theorem surrogateDiagonalTailChunk000Sub001Block006Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part019] using hcert

def TailChunk000Sub001Block006Part020SupportExplicit : Finset ℕ :=
  ([8553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part020 : ℚ :=
  (6348280603 : ℚ) / 6598820125125000

def SurrogateDiagonalTailChunk000Sub001Block006Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8553
    = surrogateDiagTailX0RatChunk000Sub001Block006Part020

theorem surrogateDiagonalTailChunk000Sub001Block006Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part020] using hcert

def TailChunk000Sub001Block006Part021SupportExplicit : Finset ℕ :=
  ([8554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part021 : ℚ :=
  (395123442175 : ℚ) / 75219108182433792

def SurrogateDiagonalTailChunk000Sub001Block006Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8554
    = surrogateDiagTailX0RatChunk000Sub001Block006Part021

theorem surrogateDiagonalTailChunk000Sub001Block006Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part021] using hcert

def TailChunk000Sub001Block006Part022SupportExplicit : Finset ℕ :=
  ([8555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part022 : ℚ :=
  (1534467358175 : ℚ) / 2226285861058904064

def SurrogateDiagonalTailChunk000Sub001Block006Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8555
    = surrogateDiagTailX0RatChunk000Sub001Block006Part022

theorem surrogateDiagonalTailChunk000Sub001Block006Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part022] using hcert

def TailChunk000Sub001Block006Part023SupportExplicit : Finset ℕ :=
  ([8557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part023 : ℚ :=
  (244158937175 : ℚ) / 664373461885632576

def SurrogateDiagonalTailChunk000Sub001Block006Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8557
    = surrogateDiagTailX0RatChunk000Sub001Block006Part023

theorem surrogateDiagonalTailChunk000Sub001Block006Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part023] using hcert

def TailChunk000Sub001Block006Part024SupportExplicit : Finset ℕ :=
  ([8558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part024 : ℚ :=
  (15909268061 : ℚ) / 4533605727037440

def SurrogateDiagonalTailChunk000Sub001Block006Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8558
    = surrogateDiagTailX0RatChunk000Sub001Block006Part024

theorem surrogateDiagonalTailChunk000Sub001Block006Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block006HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block006Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block006Part000
    + surrogateDiagTailX0RatChunk000Sub001Block006Part001
    + surrogateDiagTailX0RatChunk000Sub001Block006Part002
    + surrogateDiagTailX0RatChunk000Sub001Block006Part003
    + surrogateDiagTailX0RatChunk000Sub001Block006Part004
    + surrogateDiagTailX0RatChunk000Sub001Block006Part005
    + surrogateDiagTailX0RatChunk000Sub001Block006Part006
    + surrogateDiagTailX0RatChunk000Sub001Block006Part007
    + surrogateDiagTailX0RatChunk000Sub001Block006Part008
    + surrogateDiagTailX0RatChunk000Sub001Block006Part009

def surrogateDiagonalTailChunk000Sub001Block006MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block006Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block006Part010
    + surrogateDiagTailX0RatChunk000Sub001Block006Part011
    + surrogateDiagTailX0RatChunk000Sub001Block006Part012
    + surrogateDiagTailX0RatChunk000Sub001Block006Part013
    + surrogateDiagTailX0RatChunk000Sub001Block006Part014
    + surrogateDiagTailX0RatChunk000Sub001Block006Part015
    + surrogateDiagTailX0RatChunk000Sub001Block006Part016
    + surrogateDiagTailX0RatChunk000Sub001Block006Part017
    + surrogateDiagTailX0RatChunk000Sub001Block006Part018
    + surrogateDiagTailX0RatChunk000Sub001Block006Part019

def surrogateDiagonalTailChunk000Sub001Block006TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block006Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block006Part020
    + surrogateDiagTailX0RatChunk000Sub001Block006Part021
    + surrogateDiagTailX0RatChunk000Sub001Block006Part022
    + surrogateDiagTailX0RatChunk000Sub001Block006Part023
    + surrogateDiagTailX0RatChunk000Sub001Block006Part024

def surrogateDiagonalTailChunk000Sub001Block006Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block006HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block006MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block006TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block006 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block006Part000
    + surrogateDiagTailX0RatChunk000Sub001Block006Part001
    + surrogateDiagTailX0RatChunk000Sub001Block006Part002
    + surrogateDiagTailX0RatChunk000Sub001Block006Part003
    + surrogateDiagTailX0RatChunk000Sub001Block006Part004
    + surrogateDiagTailX0RatChunk000Sub001Block006Part005
    + surrogateDiagTailX0RatChunk000Sub001Block006Part006
    + surrogateDiagTailX0RatChunk000Sub001Block006Part007
    + surrogateDiagTailX0RatChunk000Sub001Block006Part008
    + surrogateDiagTailX0RatChunk000Sub001Block006Part009
    + surrogateDiagTailX0RatChunk000Sub001Block006Part010
    + surrogateDiagTailX0RatChunk000Sub001Block006Part011
    + surrogateDiagTailX0RatChunk000Sub001Block006Part012
    + surrogateDiagTailX0RatChunk000Sub001Block006Part013
    + surrogateDiagTailX0RatChunk000Sub001Block006Part014
    + surrogateDiagTailX0RatChunk000Sub001Block006Part015
    + surrogateDiagTailX0RatChunk000Sub001Block006Part016
    + surrogateDiagTailX0RatChunk000Sub001Block006Part017
    + surrogateDiagTailX0RatChunk000Sub001Block006Part018
    + surrogateDiagTailX0RatChunk000Sub001Block006Part019
    + surrogateDiagTailX0RatChunk000Sub001Block006Part020
    + surrogateDiagTailX0RatChunk000Sub001Block006Part021
    + surrogateDiagTailX0RatChunk000Sub001Block006Part022
    + surrogateDiagTailX0RatChunk000Sub001Block006Part023
    + surrogateDiagTailX0RatChunk000Sub001Block006Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block006_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block006Head + surrogateDiagTailX0RatChunk000Sub001Block006Mid + surrogateDiagTailX0RatChunk000Sub001Block006Tail =
      surrogateDiagTailX0RatChunk000Sub001Block006 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block006Head surrogateDiagTailX0RatChunk000Sub001Block006Mid surrogateDiagTailX0RatChunk000Sub001Block006Tail surrogateDiagTailX0RatChunk000Sub001Block006
  ring

def SurrogateDiagonalTailChunk000Sub001Block006HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block006HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block006Head

def SurrogateDiagonalTailChunk000Sub001Block006MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block006MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block006Mid

def SurrogateDiagonalTailChunk000Sub001Block006TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block006TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block006Tail

theorem surrogateDiagonalTailChunk000Sub001Block006_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block006HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block006MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block006TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block006Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block006 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block006HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block006MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block006TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block006Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block006_eq_head_add_mid_add_tail

/-- Block 007 covers tail-support indices [5175,5200) and q from 8561 to 8599. -/

def TailChunk000Sub001Block007Part000SupportExplicit : Finset ℕ :=
  ([8561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part000 : ℚ :=
  (374971447525 : ℚ) / 7226311592409257088

def SurrogateDiagonalTailChunk000Sub001Block007Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8561
    = surrogateDiagTailX0RatChunk000Sub001Block007Part000

theorem surrogateDiagonalTailChunk000Sub001Block007Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part000] using hcert

def TailChunk000Sub001Block007Part001SupportExplicit : Finset ℕ :=
  ([8562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part001 : ℚ :=
  (76317825 : ℚ) / 16540098570304

def SurrogateDiagonalTailChunk000Sub001Block007Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8562
    = surrogateDiagTailX0RatChunk000Sub001Block007Part001

theorem surrogateDiagonalTailChunk000Sub001Block007Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part001] using hcert

def TailChunk000Sub001Block007Part002SupportExplicit : Finset ℕ :=
  ([8563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8563
    = surrogateDiagTailX0RatChunk000Sub001Block007Part002

theorem surrogateDiagonalTailChunk000Sub001Block007Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part002] using hcert

def TailChunk000Sub001Block007Part003SupportExplicit : Finset ℕ :=
  ([8565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part003 : ℚ :=
  (13452753161 : ℚ) / 21623013786009600

def SurrogateDiagonalTailChunk000Sub001Block007Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8565
    = surrogateDiagTailX0RatChunk000Sub001Block007Part003

theorem surrogateDiagonalTailChunk000Sub001Block007Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part003] using hcert

def TailChunk000Sub001Block007Part004SupportExplicit : Finset ℕ :=
  ([8566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part004 : ℚ :=
  (286626390625 : ℚ) / 210161674151654322

def SurrogateDiagonalTailChunk000Sub001Block007Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8566
    = surrogateDiagTailX0RatChunk000Sub001Block007Part004

theorem surrogateDiagonalTailChunk000Sub001Block007Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part004] using hcert

def TailChunk000Sub001Block007Part005SupportExplicit : Finset ℕ :=
  ([8567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part005 : ℚ :=
  (13745693425 : ℚ) / 607484826629831808

def SurrogateDiagonalTailChunk000Sub001Block007Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8567
    = surrogateDiagTailX0RatChunk000Sub001Block007Part005

theorem surrogateDiagonalTailChunk000Sub001Block007Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part005] using hcert

def TailChunk000Sub001Block007Part006SupportExplicit : Finset ℕ :=
  ([8569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part006 : ℚ :=
  (5374642807 : ℚ) / 89597435904000000

def SurrogateDiagonalTailChunk000Sub001Block007Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8569
    = surrogateDiagTailX0RatChunk000Sub001Block007Part006

theorem surrogateDiagonalTailChunk000Sub001Block007Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part006] using hcert

def TailChunk000Sub001Block007Part007SupportExplicit : Finset ℕ :=
  ([8570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part007 : ℚ :=
  (321049671375 : ℚ) / 114562010902429696

def SurrogateDiagonalTailChunk000Sub001Block007Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8570
    = surrogateDiagTailX0RatChunk000Sub001Block007Part007

theorem surrogateDiagonalTailChunk000Sub001Block007Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part007] using hcert

def TailChunk000Sub001Block007Part008SupportExplicit : Finset ℕ :=
  ([8571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part008 : ℚ :=
  (18229325575 : ℚ) / 95065212345901056

def SurrogateDiagonalTailChunk000Sub001Block007Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8571
    = surrogateDiagTailX0RatChunk000Sub001Block007Part008

theorem surrogateDiagonalTailChunk000Sub001Block007Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part008] using hcert

def TailChunk000Sub001Block007Part009SupportExplicit : Finset ℕ :=
  ([8573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8573
    = surrogateDiagTailX0RatChunk000Sub001Block007Part009

theorem surrogateDiagonalTailChunk000Sub001Block007Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part009] using hcert

def TailChunk000Sub001Block007Part010SupportExplicit : Finset ℕ :=
  ([8574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part010 : ℚ :=
  (892920715525 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub001Block007Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8574
    = surrogateDiagTailX0RatChunk000Sub001Block007Part010

theorem surrogateDiagonalTailChunk000Sub001Block007Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part010] using hcert

def TailChunk000Sub001Block007Part011SupportExplicit : Finset ℕ :=
  ([8578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part011 : ℚ :=
  (287430015625 : ℚ) / 211342078500667392

def SurrogateDiagonalTailChunk000Sub001Block007Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8578
    = surrogateDiagTailX0RatChunk000Sub001Block007Part011

theorem surrogateDiagonalTailChunk000Sub001Block007Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part011] using hcert

def TailChunk000Sub001Block007Part012SupportExplicit : Finset ℕ :=
  ([8579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part012 : ℚ :=
  (39676866125 : ℚ) / 3739108667496339456

def SurrogateDiagonalTailChunk000Sub001Block007Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8579
    = surrogateDiagTailX0RatChunk000Sub001Block007Part012

theorem surrogateDiagonalTailChunk000Sub001Block007Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part012] using hcert

def TailChunk000Sub001Block007Part013SupportExplicit : Finset ℕ :=
  ([8581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8581
    = surrogateDiagTailX0RatChunk000Sub001Block007Part013

theorem surrogateDiagonalTailChunk000Sub001Block007Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part013] using hcert

def TailChunk000Sub001Block007Part014SupportExplicit : Finset ℕ :=
  ([8582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part014 : ℚ :=
  (252163947625 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub001Block007Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8582
    = surrogateDiagTailX0RatChunk000Sub001Block007Part014

theorem surrogateDiagonalTailChunk000Sub001Block007Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part014] using hcert

def TailChunk000Sub001Block007Part015SupportExplicit : Finset ℕ :=
  ([8583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part015 : ℚ :=
  (20457406979 : ℚ) / 53535389864985600

def SurrogateDiagonalTailChunk000Sub001Block007Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8583
    = surrogateDiagTailX0RatChunk000Sub001Block007Part015

theorem surrogateDiagonalTailChunk000Sub001Block007Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part015] using hcert

def TailChunk000Sub001Block007Part016SupportExplicit : Finset ℕ :=
  ([8585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part016 : ℚ :=
  (124579457 : ℚ) / 839028572160000

def SurrogateDiagonalTailChunk000Sub001Block007Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8585
    = surrogateDiagTailX0RatChunk000Sub001Block007Part016

theorem surrogateDiagonalTailChunk000Sub001Block007Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part016] using hcert

def TailChunk000Sub001Block007Part017SupportExplicit : Finset ℕ :=
  ([8587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part017 : ℚ :=
  (3790605157 : ℚ) / 470119426140211200

def SurrogateDiagonalTailChunk000Sub001Block007Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8587
    = surrogateDiagTailX0RatChunk000Sub001Block007Part017

theorem surrogateDiagonalTailChunk000Sub001Block007Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part017] using hcert

def TailChunk000Sub001Block007Part018SupportExplicit : Finset ℕ :=
  ([8589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part018 : ℚ :=
  (490752752675 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk000Sub001Block007Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8589
    = surrogateDiagTailX0RatChunk000Sub001Block007Part018

theorem surrogateDiagonalTailChunk000Sub001Block007Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part018] using hcert

def TailChunk000Sub001Block007Part019SupportExplicit : Finset ℕ :=
  ([8590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part019 : ℚ :=
  (460819520375 : ℚ) / 173454663162553344

def SurrogateDiagonalTailChunk000Sub001Block007Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8590
    = surrogateDiagTailX0RatChunk000Sub001Block007Part019

theorem surrogateDiagonalTailChunk000Sub001Block007Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part019] using hcert

def TailChunk000Sub001Block007Part020SupportExplicit : Finset ℕ :=
  ([8593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part020 : ℚ :=
  (176453501 : ℚ) / 8944064039116800

def SurrogateDiagonalTailChunk000Sub001Block007Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8593
    = surrogateDiagTailX0RatChunk000Sub001Block007Part020

theorem surrogateDiagonalTailChunk000Sub001Block007Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part020] using hcert

def TailChunk000Sub001Block007Part021SupportExplicit : Finset ℕ :=
  ([8594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part021 : ℚ :=
  (288503265625 : ℚ) / 212923677432402432

def SurrogateDiagonalTailChunk000Sub001Block007Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8594
    = surrogateDiagTailX0RatChunk000Sub001Block007Part021

theorem surrogateDiagonalTailChunk000Sub001Block007Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part021] using hcert

def TailChunk000Sub001Block007Part022SupportExplicit : Finset ℕ :=
  ([8597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8597
    = surrogateDiagTailX0RatChunk000Sub001Block007Part022

theorem surrogateDiagonalTailChunk000Sub001Block007Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part022] using hcert

def TailChunk000Sub001Block007Part023SupportExplicit : Finset ℕ :=
  ([8598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part023 : ℚ :=
  (897926573425 : ℚ) / 168235992045355008

def SurrogateDiagonalTailChunk000Sub001Block007Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8598
    = surrogateDiagTailX0RatChunk000Sub001Block007Part023

theorem surrogateDiagonalTailChunk000Sub001Block007Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part023] using hcert

def TailChunk000Sub001Block007Part024SupportExplicit : Finset ℕ :=
  ([8599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block007Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block007Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8599
    = surrogateDiagTailX0RatChunk000Sub001Block007Part024

theorem surrogateDiagonalTailChunk000Sub001Block007Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block007Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block007Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block007Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block007Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block007Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block007HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block007Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block007Part000
    + surrogateDiagTailX0RatChunk000Sub001Block007Part001
    + surrogateDiagTailX0RatChunk000Sub001Block007Part002
    + surrogateDiagTailX0RatChunk000Sub001Block007Part003
    + surrogateDiagTailX0RatChunk000Sub001Block007Part004
    + surrogateDiagTailX0RatChunk000Sub001Block007Part005
    + surrogateDiagTailX0RatChunk000Sub001Block007Part006
    + surrogateDiagTailX0RatChunk000Sub001Block007Part007
    + surrogateDiagTailX0RatChunk000Sub001Block007Part008
    + surrogateDiagTailX0RatChunk000Sub001Block007Part009

def surrogateDiagonalTailChunk000Sub001Block007MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block007Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block007Part010
    + surrogateDiagTailX0RatChunk000Sub001Block007Part011
    + surrogateDiagTailX0RatChunk000Sub001Block007Part012
    + surrogateDiagTailX0RatChunk000Sub001Block007Part013
    + surrogateDiagTailX0RatChunk000Sub001Block007Part014
    + surrogateDiagTailX0RatChunk000Sub001Block007Part015
    + surrogateDiagTailX0RatChunk000Sub001Block007Part016
    + surrogateDiagTailX0RatChunk000Sub001Block007Part017
    + surrogateDiagTailX0RatChunk000Sub001Block007Part018
    + surrogateDiagTailX0RatChunk000Sub001Block007Part019

def surrogateDiagonalTailChunk000Sub001Block007TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block007Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block007Part020
    + surrogateDiagTailX0RatChunk000Sub001Block007Part021
    + surrogateDiagTailX0RatChunk000Sub001Block007Part022
    + surrogateDiagTailX0RatChunk000Sub001Block007Part023
    + surrogateDiagTailX0RatChunk000Sub001Block007Part024

def surrogateDiagonalTailChunk000Sub001Block007Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block007HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block007MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block007TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block007 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block007Part000
    + surrogateDiagTailX0RatChunk000Sub001Block007Part001
    + surrogateDiagTailX0RatChunk000Sub001Block007Part002
    + surrogateDiagTailX0RatChunk000Sub001Block007Part003
    + surrogateDiagTailX0RatChunk000Sub001Block007Part004
    + surrogateDiagTailX0RatChunk000Sub001Block007Part005
    + surrogateDiagTailX0RatChunk000Sub001Block007Part006
    + surrogateDiagTailX0RatChunk000Sub001Block007Part007
    + surrogateDiagTailX0RatChunk000Sub001Block007Part008
    + surrogateDiagTailX0RatChunk000Sub001Block007Part009
    + surrogateDiagTailX0RatChunk000Sub001Block007Part010
    + surrogateDiagTailX0RatChunk000Sub001Block007Part011
    + surrogateDiagTailX0RatChunk000Sub001Block007Part012
    + surrogateDiagTailX0RatChunk000Sub001Block007Part013
    + surrogateDiagTailX0RatChunk000Sub001Block007Part014
    + surrogateDiagTailX0RatChunk000Sub001Block007Part015
    + surrogateDiagTailX0RatChunk000Sub001Block007Part016
    + surrogateDiagTailX0RatChunk000Sub001Block007Part017
    + surrogateDiagTailX0RatChunk000Sub001Block007Part018
    + surrogateDiagTailX0RatChunk000Sub001Block007Part019
    + surrogateDiagTailX0RatChunk000Sub001Block007Part020
    + surrogateDiagTailX0RatChunk000Sub001Block007Part021
    + surrogateDiagTailX0RatChunk000Sub001Block007Part022
    + surrogateDiagTailX0RatChunk000Sub001Block007Part023
    + surrogateDiagTailX0RatChunk000Sub001Block007Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block007_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block007Head + surrogateDiagTailX0RatChunk000Sub001Block007Mid + surrogateDiagTailX0RatChunk000Sub001Block007Tail =
      surrogateDiagTailX0RatChunk000Sub001Block007 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block007Head surrogateDiagTailX0RatChunk000Sub001Block007Mid surrogateDiagTailX0RatChunk000Sub001Block007Tail surrogateDiagTailX0RatChunk000Sub001Block007
  ring

def SurrogateDiagonalTailChunk000Sub001Block007HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block007HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block007Head

def SurrogateDiagonalTailChunk000Sub001Block007MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block007MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block007Mid

def SurrogateDiagonalTailChunk000Sub001Block007TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block007TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block007Tail

theorem surrogateDiagonalTailChunk000Sub001Block007_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block007HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block007MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block007TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block007Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block007 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block007HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block007MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block007TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block007Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block007_eq_head_add_mid_add_tail

/-- Block 008 covers tail-support indices [5200,5225) and q from 8601 to 8639. -/

def TailChunk000Sub001Block008Part000SupportExplicit : Finset ℕ :=
  ([8601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part000 : ℚ :=
  (40658992399 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk000Sub001Block008Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8601
    = surrogateDiagTailX0RatChunk000Sub001Block008Part000

theorem surrogateDiagonalTailChunk000Sub001Block008Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part000] using hcert

def TailChunk000Sub001Block008Part001SupportExplicit : Finset ℕ :=
  ([8602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part001 : ℚ :=
  (39163082929 : ℚ) / 15355271656243200

def SurrogateDiagonalTailChunk000Sub001Block008Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8602
    = surrogateDiagTailX0RatChunk000Sub001Block008Part001

theorem surrogateDiagonalTailChunk000Sub001Block008Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part001] using hcert

def TailChunk000Sub001Block008Part002SupportExplicit : Finset ℕ :=
  ([8603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part002 : ℚ :=
  (378644241925 : ℚ) / 7369284573591717888

def SurrogateDiagonalTailChunk000Sub001Block008Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8603
    = surrogateDiagTailX0RatChunk000Sub001Block008Part002

theorem surrogateDiagonalTailChunk000Sub001Block008Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part002] using hcert

def TailChunk000Sub001Block008Part003SupportExplicit : Finset ℕ :=
  ([8605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part003 : ℚ :=
  (11114565581 : ℚ) / 112049676622233600

def SurrogateDiagonalTailChunk000Sub001Block008Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8605
    = surrogateDiagTailX0RatChunk000Sub001Block008Part003

theorem surrogateDiagonalTailChunk000Sub001Block008Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part003] using hcert

def TailChunk000Sub001Block008Part004SupportExplicit : Finset ℕ :=
  ([8606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part004 : ℚ :=
  (4797072919 : ℚ) / 2732908456396800

def SurrogateDiagonalTailChunk000Sub001Block008Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8606
    = surrogateDiagTailX0RatChunk000Sub001Block008Part004

theorem surrogateDiagonalTailChunk000Sub001Block008Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part004] using hcert

def TailChunk000Sub001Block008Part005SupportExplicit : Finset ℕ :=
  ([8607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part005 : ℚ :=
  (1499640953 : ℚ) / 3149909856000000

def SurrogateDiagonalTailChunk000Sub001Block008Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8607
    = surrogateDiagTailX0RatChunk000Sub001Block008Part005

theorem surrogateDiagonalTailChunk000Sub001Block008Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part005] using hcert

def TailChunk000Sub001Block008Part006SupportExplicit : Finset ℕ :=
  ([8609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block008Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8609
    = surrogateDiagTailX0RatChunk000Sub001Block008Part006

theorem surrogateDiagonalTailChunk000Sub001Block008Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part006] using hcert

def TailChunk000Sub001Block008Part007SupportExplicit : Finset ℕ :=
  ([8610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part007 : ℚ :=
  (1218922309 : ℚ) / 75512571494400

def SurrogateDiagonalTailChunk000Sub001Block008Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8610
    = surrogateDiagTailX0RatChunk000Sub001Block008Part007

theorem surrogateDiagonalTailChunk000Sub001Block008Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part007] using hcert

def TailChunk000Sub001Block008Part008SupportExplicit : Finset ℕ :=
  ([8611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part008 : ℚ :=
  (2211377225 : ℚ) / 484313911122981888

def SurrogateDiagonalTailChunk000Sub001Block008Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8611
    = surrogateDiagTailX0RatChunk000Sub001Block008Part008

theorem surrogateDiagonalTailChunk000Sub001Block008Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part008] using hcert

def TailChunk000Sub001Block008Part009SupportExplicit : Finset ℕ :=
  ([8614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part009 : ℚ :=
  (282457089025 : ℚ) / 190111692190851072

def SurrogateDiagonalTailChunk000Sub001Block008Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8614
    = surrogateDiagTailX0RatChunk000Sub001Block008Part009

theorem surrogateDiagonalTailChunk000Sub001Block008Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part009] using hcert

def TailChunk000Sub001Block008Part010SupportExplicit : Finset ℕ :=
  ([8615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part010 : ℚ :=
  (19893518275 : ℚ) / 201020977885625856

def SurrogateDiagonalTailChunk000Sub001Block008Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8615
    = surrogateDiagTailX0RatChunk000Sub001Block008Part010

theorem surrogateDiagonalTailChunk000Sub001Block008Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part010] using hcert

def TailChunk000Sub001Block008Part011SupportExplicit : Finset ℕ :=
  ([8617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part011 : ℚ :=
  (15194900173 : ℚ) / 296696414153347200

def SurrogateDiagonalTailChunk000Sub001Block008Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8617
    = surrogateDiagTailX0RatChunk000Sub001Block008Part011

theorem surrogateDiagonalTailChunk000Sub001Block008Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part011] using hcert

def TailChunk000Sub001Block008Part012SupportExplicit : Finset ℕ :=
  ([8618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part012 : ℚ :=
  (561201317 : ℚ) / 367280801672040

def SurrogateDiagonalTailChunk000Sub001Block008Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8618
    = surrogateDiagTailX0RatChunk000Sub001Block008Part012

theorem surrogateDiagonalTailChunk000Sub001Block008Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part012] using hcert

def TailChunk000Sub001Block008Part013SupportExplicit : Finset ℕ :=
  ([8621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part013 : ℚ :=
  (246793328275 : ℚ) / 675952683345248256

def SurrogateDiagonalTailChunk000Sub001Block008Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8621
    = surrogateDiagTailX0RatChunk000Sub001Block008Part013

theorem surrogateDiagonalTailChunk000Sub001Block008Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part013] using hcert

def TailChunk000Sub001Block008Part014SupportExplicit : Finset ℕ :=
  ([8623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part014 : ℚ :=
  (1161814515625 : ℚ) / 3454609330187705682

def SurrogateDiagonalTailChunk000Sub001Block008Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8623
    = surrogateDiagTailX0RatChunk000Sub001Block008Part014

theorem surrogateDiagonalTailChunk000Sub001Block008Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part014] using hcert

def TailChunk000Sub001Block008Part015SupportExplicit : Finset ℕ :=
  ([8626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part015 : ℚ :=
  (712755156475 : ℚ) / 228259773070528896

def SurrogateDiagonalTailChunk000Sub001Block008Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8626
    = surrogateDiagTailX0RatChunk000Sub001Block008Part015

theorem surrogateDiagonalTailChunk000Sub001Block008Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part015] using hcert

def TailChunk000Sub001Block008Part016SupportExplicit : Finset ℕ :=
  ([8627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part016 : ℚ :=
  (1162892640625 : ℚ) / 3461024573270963922

def SurrogateDiagonalTailChunk000Sub001Block008Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8627
    = surrogateDiagTailX0RatChunk000Sub001Block008Part016

theorem surrogateDiagonalTailChunk000Sub001Block008Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part016] using hcert

def TailChunk000Sub001Block008Part017SupportExplicit : Finset ℕ :=
  ([8629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part017 : ℚ :=
  (1163431890625 : ℚ) / 3464235543319110432

def SurrogateDiagonalTailChunk000Sub001Block008Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8629
    = surrogateDiagTailX0RatChunk000Sub001Block008Part017

theorem surrogateDiagonalTailChunk000Sub001Block008Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part017] using hcert

def TailChunk000Sub001Block008Part018SupportExplicit : Finset ℕ :=
  ([8630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part018 : ℚ :=
  (836641880375 : ℚ) / 176711938820219904

def SurrogateDiagonalTailChunk000Sub001Block008Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8630
    = surrogateDiagTailX0RatChunk000Sub001Block008Part018

theorem surrogateDiagonalTailChunk000Sub001Block008Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part018] using hcert

def TailChunk000Sub001Block008Part019SupportExplicit : Finset ℕ :=
  ([8633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part019 : ℚ :=
  (205367211925 : ℚ) / 578921660116107264

def SurrogateDiagonalTailChunk000Sub001Block008Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8633
    = surrogateDiagTailX0RatChunk000Sub001Block008Part019

theorem surrogateDiagonalTailChunk000Sub001Block008Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part019] using hcert

def TailChunk000Sub001Block008Part020SupportExplicit : Finset ℕ :=
  ([8634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part020 : ℚ :=
  (77606625 : ℚ) / 17103915233344

def SurrogateDiagonalTailChunk000Sub001Block008Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8634
    = surrogateDiagTailX0RatChunk000Sub001Block008Part020

theorem surrogateDiagonalTailChunk000Sub001Block008Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part020] using hcert

def TailChunk000Sub001Block008Part021SupportExplicit : Finset ℕ :=
  ([8635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part021 : ℚ :=
  (4510255421 : ℚ) / 5832461234995200

def SurrogateDiagonalTailChunk000Sub001Block008Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8635
    = surrogateDiagTailX0RatChunk000Sub001Block008Part021

theorem surrogateDiagonalTailChunk000Sub001Block008Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part021] using hcert

def TailChunk000Sub001Block008Part022SupportExplicit : Finset ℕ :=
  ([8637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part022 : ℚ :=
  (647360064925 : ℚ) / 686198885909274912

def SurrogateDiagonalTailChunk000Sub001Block008Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8637
    = surrogateDiagTailX0RatChunk000Sub001Block008Part022

theorem surrogateDiagonalTailChunk000Sub001Block008Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part022] using hcert

def TailChunk000Sub001Block008Part023SupportExplicit : Finset ℕ :=
  ([8638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part023 : ℚ :=
  (255464842375 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub001Block008Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8638
    = surrogateDiagTailX0RatChunk000Sub001Block008Part023

theorem surrogateDiagonalTailChunk000Sub001Block008Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part023] using hcert

def TailChunk000Sub001Block008Part024SupportExplicit : Finset ℕ :=
  ([8639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part024 : ℚ :=
  (750229444675 : ℚ) / 2098693614866254848

def SurrogateDiagonalTailChunk000Sub001Block008Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8639
    = surrogateDiagTailX0RatChunk000Sub001Block008Part024

theorem surrogateDiagonalTailChunk000Sub001Block008Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block008HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block008Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block008Part000
    + surrogateDiagTailX0RatChunk000Sub001Block008Part001
    + surrogateDiagTailX0RatChunk000Sub001Block008Part002
    + surrogateDiagTailX0RatChunk000Sub001Block008Part003
    + surrogateDiagTailX0RatChunk000Sub001Block008Part004
    + surrogateDiagTailX0RatChunk000Sub001Block008Part005
    + surrogateDiagTailX0RatChunk000Sub001Block008Part006
    + surrogateDiagTailX0RatChunk000Sub001Block008Part007
    + surrogateDiagTailX0RatChunk000Sub001Block008Part008
    + surrogateDiagTailX0RatChunk000Sub001Block008Part009

def surrogateDiagonalTailChunk000Sub001Block008MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block008Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block008Part010
    + surrogateDiagTailX0RatChunk000Sub001Block008Part011
    + surrogateDiagTailX0RatChunk000Sub001Block008Part012
    + surrogateDiagTailX0RatChunk000Sub001Block008Part013
    + surrogateDiagTailX0RatChunk000Sub001Block008Part014
    + surrogateDiagTailX0RatChunk000Sub001Block008Part015
    + surrogateDiagTailX0RatChunk000Sub001Block008Part016
    + surrogateDiagTailX0RatChunk000Sub001Block008Part017
    + surrogateDiagTailX0RatChunk000Sub001Block008Part018
    + surrogateDiagTailX0RatChunk000Sub001Block008Part019

def surrogateDiagonalTailChunk000Sub001Block008TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block008Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block008Part020
    + surrogateDiagTailX0RatChunk000Sub001Block008Part021
    + surrogateDiagTailX0RatChunk000Sub001Block008Part022
    + surrogateDiagTailX0RatChunk000Sub001Block008Part023
    + surrogateDiagTailX0RatChunk000Sub001Block008Part024

def surrogateDiagonalTailChunk000Sub001Block008Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block008HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block008MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block008TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block008 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block008Part000
    + surrogateDiagTailX0RatChunk000Sub001Block008Part001
    + surrogateDiagTailX0RatChunk000Sub001Block008Part002
    + surrogateDiagTailX0RatChunk000Sub001Block008Part003
    + surrogateDiagTailX0RatChunk000Sub001Block008Part004
    + surrogateDiagTailX0RatChunk000Sub001Block008Part005
    + surrogateDiagTailX0RatChunk000Sub001Block008Part006
    + surrogateDiagTailX0RatChunk000Sub001Block008Part007
    + surrogateDiagTailX0RatChunk000Sub001Block008Part008
    + surrogateDiagTailX0RatChunk000Sub001Block008Part009
    + surrogateDiagTailX0RatChunk000Sub001Block008Part010
    + surrogateDiagTailX0RatChunk000Sub001Block008Part011
    + surrogateDiagTailX0RatChunk000Sub001Block008Part012
    + surrogateDiagTailX0RatChunk000Sub001Block008Part013
    + surrogateDiagTailX0RatChunk000Sub001Block008Part014
    + surrogateDiagTailX0RatChunk000Sub001Block008Part015
    + surrogateDiagTailX0RatChunk000Sub001Block008Part016
    + surrogateDiagTailX0RatChunk000Sub001Block008Part017
    + surrogateDiagTailX0RatChunk000Sub001Block008Part018
    + surrogateDiagTailX0RatChunk000Sub001Block008Part019
    + surrogateDiagTailX0RatChunk000Sub001Block008Part020
    + surrogateDiagTailX0RatChunk000Sub001Block008Part021
    + surrogateDiagTailX0RatChunk000Sub001Block008Part022
    + surrogateDiagTailX0RatChunk000Sub001Block008Part023
    + surrogateDiagTailX0RatChunk000Sub001Block008Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block008_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block008Head + surrogateDiagTailX0RatChunk000Sub001Block008Mid + surrogateDiagTailX0RatChunk000Sub001Block008Tail =
      surrogateDiagTailX0RatChunk000Sub001Block008 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block008Head surrogateDiagTailX0RatChunk000Sub001Block008Mid surrogateDiagTailX0RatChunk000Sub001Block008Tail surrogateDiagTailX0RatChunk000Sub001Block008
  ring

def SurrogateDiagonalTailChunk000Sub001Block008HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block008HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block008Head

def SurrogateDiagonalTailChunk000Sub001Block008MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block008MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block008Mid

def SurrogateDiagonalTailChunk000Sub001Block008TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block008TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block008Tail

theorem surrogateDiagonalTailChunk000Sub001Block008_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block008HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block008MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block008TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block008Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block008 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block008HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block008MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block008TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block008Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block008_eq_head_add_mid_add_tail

/-- Block 009 covers tail-support indices [5225,5250) and q from 8641 to 8682. -/

def TailChunk000Sub001Block009Part000SupportExplicit : Finset ℕ :=
  ([8641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part000 : ℚ :=
  (1866672025 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub001Block009Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8641
    = surrogateDiagTailX0RatChunk000Sub001Block009Part000

theorem surrogateDiagonalTailChunk000Sub001Block009Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part000] using hcert

def TailChunk000Sub001Block009Part001SupportExplicit : Finset ℕ :=
  ([8642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part001 : ℚ :=
  (187895080425 : ℚ) / 122900767624183808

def SurrogateDiagonalTailChunk000Sub001Block009Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8642
    = surrogateDiagTailX0RatChunk000Sub001Block009Part001

theorem surrogateDiagonalTailChunk000Sub001Block009Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part001] using hcert

def TailChunk000Sub001Block009Part002SupportExplicit : Finset ℕ :=
  ([8643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part002 : ℚ :=
  (2466959499475 : ℚ) / 2362216753371138048

def SurrogateDiagonalTailChunk000Sub001Block009Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8643
    = surrogateDiagTailX0RatChunk000Sub001Block009Part002

theorem surrogateDiagonalTailChunk000Sub001Block009Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part002] using hcert

def TailChunk000Sub001Block009Part003SupportExplicit : Finset ℕ :=
  ([8645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part003 : ℚ :=
  (1136025889625 : ℚ) / 902935721419997184

def SurrogateDiagonalTailChunk000Sub001Block009Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8645
    = surrogateDiagTailX0RatChunk000Sub001Block009Part003

theorem surrogateDiagonalTailChunk000Sub001Block009Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part003] using hcert

def TailChunk000Sub001Block009Part004SupportExplicit : Finset ℕ :=
  ([8646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part004 : ℚ :=
  (8165033203 : ℚ) / 1142668488000000

def SurrogateDiagonalTailChunk000Sub001Block009Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8646
    = surrogateDiagTailX0RatChunk000Sub001Block009Part004

theorem surrogateDiagonalTailChunk000Sub001Block009Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part004] using hcert

def TailChunk000Sub001Block009Part005SupportExplicit : Finset ℕ :=
  ([8647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part005 : ℚ :=
  (1168290765625 : ℚ) / 3493234915404034482

def SurrogateDiagonalTailChunk000Sub001Block009Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8647
    = surrogateDiagTailX0RatChunk000Sub001Block009Part005

theorem surrogateDiagonalTailChunk000Sub001Block009Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part005] using hcert

def TailChunk000Sub001Block009Part006SupportExplicit : Finset ℕ :=
  ([8651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part006 : ℚ :=
  (640933381 : ℚ) / 1778467622400000

def SurrogateDiagonalTailChunk000Sub001Block009Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8651
    = surrogateDiagTailX0RatChunk000Sub001Block009Part006

theorem surrogateDiagonalTailChunk000Sub001Block009Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part006] using hcert

def TailChunk000Sub001Block009Part007SupportExplicit : Finset ℕ :=
  ([8653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part007 : ℚ :=
  (4279863503875 : ℚ) / 10913439334665289728

def SurrogateDiagonalTailChunk000Sub001Block009Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8653
    = surrogateDiagTailX0RatChunk000Sub001Block009Part007

theorem surrogateDiagonalTailChunk000Sub001Block009Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part007] using hcert

def TailChunk000Sub001Block009Part008SupportExplicit : Finset ℕ :=
  ([8654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part008 : ℚ :=
  (292545765625 : ℚ) / 218933856893385522

def SurrogateDiagonalTailChunk000Sub001Block009Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8654
    = surrogateDiagTailX0RatChunk000Sub001Block009Part008

theorem surrogateDiagonalTailChunk000Sub001Block009Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part008] using hcert

def TailChunk000Sub001Block009Part009SupportExplicit : Finset ℕ :=
  ([8655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part009 : ℚ :=
  (107290207675 : ℚ) / 62633147300315136

def SurrogateDiagonalTailChunk000Sub001Block009Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8655
    = surrogateDiagTailX0RatChunk000Sub001Block009Part009

theorem surrogateDiagonalTailChunk000Sub001Block009Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part009] using hcert

def TailChunk000Sub001Block009Part010SupportExplicit : Finset ℕ :=
  ([8657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part010 : ℚ :=
  (8116051769 : ℚ) / 19087411599776160

def SurrogateDiagonalTailChunk000Sub001Block009Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8657
    = surrogateDiagTailX0RatChunk000Sub001Block009Part010

theorem surrogateDiagonalTailChunk000Sub001Block009Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part010] using hcert

def TailChunk000Sub001Block009Part011SupportExplicit : Finset ℕ :=
  ([8659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part011 : ℚ :=
  (207011316875 : ℚ) / 420177931097342976

def SurrogateDiagonalTailChunk000Sub001Block009Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8659
    = surrogateDiagTailX0RatChunk000Sub001Block009Part011

theorem surrogateDiagonalTailChunk000Sub001Block009Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part011] using hcert

def TailChunk000Sub001Block009Part012SupportExplicit : Finset ℕ :=
  ([8661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part012 : ℚ :=
  (2082873711325 : ℚ) / 2775441952115584128

def SurrogateDiagonalTailChunk000Sub001Block009Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8661
    = surrogateDiagTailX0RatChunk000Sub001Block009Part012

theorem surrogateDiagonalTailChunk000Sub001Block009Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part012] using hcert

def TailChunk000Sub001Block009Part013SupportExplicit : Finset ℕ :=
  ([8662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part013 : ℚ :=
  (1827812299 : ℚ) / 1244927335680000

def SurrogateDiagonalTailChunk000Sub001Block009Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8662
    = surrogateDiagTailX0RatChunk000Sub001Block009Part013

theorem surrogateDiagonalTailChunk000Sub001Block009Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part013] using hcert

def TailChunk000Sub001Block009Part014SupportExplicit : Finset ℕ :=
  ([8663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part014 : ℚ :=
  (1172618265625 : ℚ) / 3519164638876547442

def SurrogateDiagonalTailChunk000Sub001Block009Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8663
    = surrogateDiagTailX0RatChunk000Sub001Block009Part014

theorem surrogateDiagonalTailChunk000Sub001Block009Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part014] using hcert

def TailChunk000Sub001Block009Part015SupportExplicit : Finset ℕ :=
  ([8665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part015 : ℚ :=
  (1125525755775 : ℚ) / 1920158681553534976

def SurrogateDiagonalTailChunk000Sub001Block009Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8665
    = surrogateDiagTailX0RatChunk000Sub001Block009Part015

theorem surrogateDiagonalTailChunk000Sub001Block009Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part015] using hcert

def TailChunk000Sub001Block009Part016SupportExplicit : Finset ℕ :=
  ([8666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part016 : ℚ :=
  (257123353825 : ℚ) / 118175043121127712

def SurrogateDiagonalTailChunk000Sub001Block009Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8666
    = surrogateDiagTailX0RatChunk000Sub001Block009Part016

theorem surrogateDiagonalTailChunk000Sub001Block009Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part016] using hcert

def TailChunk000Sub001Block009Part017SupportExplicit : Finset ℕ :=
  ([8669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part017 : ℚ :=
  (1174243140625 : ℚ) / 3528925404003370272

def SurrogateDiagonalTailChunk000Sub001Block009Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8669
    = surrogateDiagTailX0RatChunk000Sub001Block009Part017

theorem surrogateDiagonalTailChunk000Sub001Block009Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part017] using hcert

def TailChunk000Sub001Block009Part018SupportExplicit : Finset ℕ :=
  ([8671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part018 : ℚ :=
  (1249502846225 : ℚ) / 2488590489148194816

def SurrogateDiagonalTailChunk000Sub001Block009Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8671
    = surrogateDiagTailX0RatChunk000Sub001Block009Part018

theorem surrogateDiagonalTailChunk000Sub001Block009Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part018] using hcert

def TailChunk000Sub001Block009Part019SupportExplicit : Finset ℕ :=
  ([8674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part019 : ℚ :=
  (293899515625 : ℚ) / 220965240713060352

def SurrogateDiagonalTailChunk000Sub001Block009Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8674
    = surrogateDiagTailX0RatChunk000Sub001Block009Part019

theorem surrogateDiagonalTailChunk000Sub001Block009Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part019] using hcert

def TailChunk000Sub001Block009Part020SupportExplicit : Finset ℕ :=
  ([8677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part020 : ℚ :=
  (1176411390625 : ℚ) / 3541971325049847072

def SurrogateDiagonalTailChunk000Sub001Block009Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8677
    = surrogateDiagTailX0RatChunk000Sub001Block009Part020

theorem surrogateDiagonalTailChunk000Sub001Block009Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part020] using hcert

def TailChunk000Sub001Block009Part021SupportExplicit : Finset ℕ :=
  ([8678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part021 : ℚ :=
  (294170640625 : ℚ) / 221373207815615442

def SurrogateDiagonalTailChunk000Sub001Block009Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8678
    = surrogateDiagTailX0RatChunk000Sub001Block009Part021

theorem surrogateDiagonalTailChunk000Sub001Block009Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part021] using hcert

def TailChunk000Sub001Block009Part022SupportExplicit : Finset ℕ :=
  ([8679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part022 : ℚ :=
  (9207612673 : ℚ) / 7540705817195520

def SurrogateDiagonalTailChunk000Sub001Block009Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8679
    = surrogateDiagTailX0RatChunk000Sub001Block009Part022

theorem surrogateDiagonalTailChunk000Sub001Block009Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part022] using hcert

def TailChunk000Sub001Block009Part023SupportExplicit : Finset ℕ :=
  ([8681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part023 : ℚ :=
  (1883994025 : ℚ) / 5677612533207552

def SurrogateDiagonalTailChunk000Sub001Block009Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8681
    = surrogateDiagTailX0RatChunk000Sub001Block009Part023

theorem surrogateDiagonalTailChunk000Sub001Block009Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part023] using hcert

def TailChunk000Sub001Block009Part024SupportExplicit : Finset ℕ :=
  ([8682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part024 : ℚ :=
  (26157275 : ℚ) / 5829239625408

def SurrogateDiagonalTailChunk000Sub001Block009Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8682
    = surrogateDiagTailX0RatChunk000Sub001Block009Part024

theorem surrogateDiagonalTailChunk000Sub001Block009Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block009HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block009Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block009Part000
    + surrogateDiagTailX0RatChunk000Sub001Block009Part001
    + surrogateDiagTailX0RatChunk000Sub001Block009Part002
    + surrogateDiagTailX0RatChunk000Sub001Block009Part003
    + surrogateDiagTailX0RatChunk000Sub001Block009Part004
    + surrogateDiagTailX0RatChunk000Sub001Block009Part005
    + surrogateDiagTailX0RatChunk000Sub001Block009Part006
    + surrogateDiagTailX0RatChunk000Sub001Block009Part007
    + surrogateDiagTailX0RatChunk000Sub001Block009Part008
    + surrogateDiagTailX0RatChunk000Sub001Block009Part009

def surrogateDiagonalTailChunk000Sub001Block009MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block009Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block009Part010
    + surrogateDiagTailX0RatChunk000Sub001Block009Part011
    + surrogateDiagTailX0RatChunk000Sub001Block009Part012
    + surrogateDiagTailX0RatChunk000Sub001Block009Part013
    + surrogateDiagTailX0RatChunk000Sub001Block009Part014
    + surrogateDiagTailX0RatChunk000Sub001Block009Part015
    + surrogateDiagTailX0RatChunk000Sub001Block009Part016
    + surrogateDiagTailX0RatChunk000Sub001Block009Part017
    + surrogateDiagTailX0RatChunk000Sub001Block009Part018
    + surrogateDiagTailX0RatChunk000Sub001Block009Part019

def surrogateDiagonalTailChunk000Sub001Block009TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block009Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block009Part020
    + surrogateDiagTailX0RatChunk000Sub001Block009Part021
    + surrogateDiagTailX0RatChunk000Sub001Block009Part022
    + surrogateDiagTailX0RatChunk000Sub001Block009Part023
    + surrogateDiagTailX0RatChunk000Sub001Block009Part024

def surrogateDiagonalTailChunk000Sub001Block009Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block009HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block009MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block009TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block009 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block009Part000
    + surrogateDiagTailX0RatChunk000Sub001Block009Part001
    + surrogateDiagTailX0RatChunk000Sub001Block009Part002
    + surrogateDiagTailX0RatChunk000Sub001Block009Part003
    + surrogateDiagTailX0RatChunk000Sub001Block009Part004
    + surrogateDiagTailX0RatChunk000Sub001Block009Part005
    + surrogateDiagTailX0RatChunk000Sub001Block009Part006
    + surrogateDiagTailX0RatChunk000Sub001Block009Part007
    + surrogateDiagTailX0RatChunk000Sub001Block009Part008
    + surrogateDiagTailX0RatChunk000Sub001Block009Part009
    + surrogateDiagTailX0RatChunk000Sub001Block009Part010
    + surrogateDiagTailX0RatChunk000Sub001Block009Part011
    + surrogateDiagTailX0RatChunk000Sub001Block009Part012
    + surrogateDiagTailX0RatChunk000Sub001Block009Part013
    + surrogateDiagTailX0RatChunk000Sub001Block009Part014
    + surrogateDiagTailX0RatChunk000Sub001Block009Part015
    + surrogateDiagTailX0RatChunk000Sub001Block009Part016
    + surrogateDiagTailX0RatChunk000Sub001Block009Part017
    + surrogateDiagTailX0RatChunk000Sub001Block009Part018
    + surrogateDiagTailX0RatChunk000Sub001Block009Part019
    + surrogateDiagTailX0RatChunk000Sub001Block009Part020
    + surrogateDiagTailX0RatChunk000Sub001Block009Part021
    + surrogateDiagTailX0RatChunk000Sub001Block009Part022
    + surrogateDiagTailX0RatChunk000Sub001Block009Part023
    + surrogateDiagTailX0RatChunk000Sub001Block009Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block009_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block009Head + surrogateDiagTailX0RatChunk000Sub001Block009Mid + surrogateDiagTailX0RatChunk000Sub001Block009Tail =
      surrogateDiagTailX0RatChunk000Sub001Block009 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block009Head surrogateDiagTailX0RatChunk000Sub001Block009Mid surrogateDiagTailX0RatChunk000Sub001Block009Tail surrogateDiagTailX0RatChunk000Sub001Block009
  ring

def SurrogateDiagonalTailChunk000Sub001Block009HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block009HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block009Head

def SurrogateDiagonalTailChunk000Sub001Block009MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block009MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block009Mid

def SurrogateDiagonalTailChunk000Sub001Block009TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block009TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block009Tail

theorem surrogateDiagonalTailChunk000Sub001Block009_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block009HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block009MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block009TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block009Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block009 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block009HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block009MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block009TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block009Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block009_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
