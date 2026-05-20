import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [0,1). -/

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

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
