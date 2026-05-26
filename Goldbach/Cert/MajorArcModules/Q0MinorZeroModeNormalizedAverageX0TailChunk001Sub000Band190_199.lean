import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [190,200). -/

/-- Block 190 covers tail-support indices [14750,14775) and q from 24310 to 24351. -/

def TailChunk001Sub000Block190Part000SupportExplicit : Finset ℕ :=
  ([24310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part000 : ℚ :=
  (41116967221 : ℚ) / 347961929446195200

def SurrogateDiagonalTailChunk001Sub000Block190Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24310
    = surrogateDiagTailX0RatChunk001Sub000Block190Part000

theorem surrogateDiagonalTailChunk001Sub000Block190Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part000] using hcert

def TailChunk001Sub000Block190Part001SupportExplicit : Finset ℕ :=
  ([24311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part001 : ℚ :=
  (65707004791 : ℚ) / 15372610067232000000

def SurrogateDiagonalTailChunk001Sub000Block190Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24311
    = surrogateDiagTailX0RatChunk001Sub000Block190Part001

theorem surrogateDiagonalTailChunk001Sub000Block190Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part001] using hcert

def TailChunk001Sub000Block190Part002SupportExplicit : Finset ℕ :=
  ([24313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part002 : ℚ :=
  (7499701879 : ℚ) / 31449492556559155200

def SurrogateDiagonalTailChunk001Sub000Block190Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24313
    = surrogateDiagTailX0RatChunk001Sub000Block190Part002

theorem surrogateDiagonalTailChunk001Sub000Block190Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part002] using hcert

def TailChunk001Sub000Block190Part003SupportExplicit : Finset ℕ :=
  ([24314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block190Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24314
    = surrogateDiagTailX0RatChunk001Sub000Block190Part003

theorem surrogateDiagonalTailChunk001Sub000Block190Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part003] using hcert

def TailChunk001Sub000Block190Part004SupportExplicit : Finset ℕ :=
  ([24315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part004 : ℚ :=
  (68937882089 : ℚ) / 1410837064718745600

def SurrogateDiagonalTailChunk001Sub000Block190Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24315
    = surrogateDiagTailX0RatChunk001Sub000Block190Part004

theorem surrogateDiagonalTailChunk001Sub000Block190Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part004] using hcert

def TailChunk001Sub000Block190Part005SupportExplicit : Finset ℕ :=
  ([24317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block190Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24317
    = surrogateDiagTailX0RatChunk001Sub000Block190Part005

theorem surrogateDiagonalTailChunk001Sub000Block190Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part005] using hcert

def TailChunk001Sub000Block190Part006SupportExplicit : Finset ℕ :=
  ([24319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part006 : ℚ :=
  (57915726575 : ℚ) / 410944979019664794624

def SurrogateDiagonalTailChunk001Sub000Block190Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24319
    = surrogateDiagTailX0RatChunk001Sub000Block190Part006

theorem surrogateDiagonalTailChunk001Sub000Block190Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part006] using hcert

def TailChunk001Sub000Block190Part007SupportExplicit : Finset ℕ :=
  ([24322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block190Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24322
    = surrogateDiagTailX0RatChunk001Sub000Block190Part007

theorem surrogateDiagonalTailChunk001Sub000Block190Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part007] using hcert

def TailChunk001Sub000Block190Part008SupportExplicit : Finset ℕ :=
  ([24323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part008 : ℚ :=
  (17631145669 : ℚ) / 25361694131857459200

def SurrogateDiagonalTailChunk001Sub000Block190Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24323
    = surrogateDiagTailX0RatChunk001Sub000Block190Part008

theorem surrogateDiagonalTailChunk001Sub000Block190Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part008] using hcert

def TailChunk001Sub000Block190Part009SupportExplicit : Finset ℕ :=
  ([24326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block190Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24326
    = surrogateDiagTailX0RatChunk001Sub000Block190Part009

theorem surrogateDiagonalTailChunk001Sub000Block190Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part009] using hcert

def TailChunk001Sub000Block190Part010SupportExplicit : Finset ℕ :=
  ([24329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block190Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24329
    = surrogateDiagTailX0RatChunk001Sub000Block190Part010

theorem surrogateDiagonalTailChunk001Sub000Block190Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part010] using hcert

def TailChunk001Sub000Block190Part011SupportExplicit : Finset ℕ :=
  ([24330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part011 : ℚ :=
  (1775495353 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk001Sub000Block190Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24330
    = surrogateDiagTailX0RatChunk001Sub000Block190Part011

theorem surrogateDiagonalTailChunk001Sub000Block190Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part011] using hcert

def TailChunk001Sub000Block190Part012SupportExplicit : Finset ℕ :=
  ([24331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part012 : ℚ :=
  (271810221175 : ℚ) / 757940403799245047808

def SurrogateDiagonalTailChunk001Sub000Block190Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24331
    = surrogateDiagTailX0RatChunk001Sub000Block190Part012

theorem surrogateDiagonalTailChunk001Sub000Block190Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part012] using hcert

def TailChunk001Sub000Block190Part013SupportExplicit : Finset ℕ :=
  ([24333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part013 : ℚ :=
  (16445524939 : ℚ) / 692293493158029120

def SurrogateDiagonalTailChunk001Sub000Block190Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24333
    = surrogateDiagTailX0RatChunk001Sub000Block190Part013

theorem surrogateDiagonalTailChunk001Sub000Block190Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part013] using hcert

def TailChunk001Sub000Block190Part014SupportExplicit : Finset ℕ :=
  ([24335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part014 : ℚ :=
  (620673707 : ℚ) / 118107340008652800

def SurrogateDiagonalTailChunk001Sub000Block190Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24335
    = surrogateDiagTailX0RatChunk001Sub000Block190Part014

theorem surrogateDiagonalTailChunk001Sub000Block190Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part014] using hcert

def TailChunk001Sub000Block190Part015SupportExplicit : Finset ℕ :=
  ([24337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block190Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24337
    = surrogateDiagTailX0RatChunk001Sub000Block190Part015

theorem surrogateDiagonalTailChunk001Sub000Block190Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part015] using hcert

def TailChunk001Sub000Block190Part016SupportExplicit : Finset ℕ :=
  ([24338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part016 : ℚ :=
  (1263706375 : ℚ) / 607484826629831808

def SurrogateDiagonalTailChunk001Sub000Block190Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24338
    = surrogateDiagTailX0RatChunk001Sub000Block190Part016

theorem surrogateDiagonalTailChunk001Sub000Block190Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part016] using hcert

def TailChunk001Sub000Block190Part017SupportExplicit : Finset ℕ :=
  ([24339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part017 : ℚ :=
  (28483371113 : ℚ) / 564334825887498240

def SurrogateDiagonalTailChunk001Sub000Block190Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24339
    = surrogateDiagTailX0RatChunk001Sub000Block190Part017

theorem surrogateDiagonalTailChunk001Sub000Block190Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part017] using hcert

def TailChunk001Sub000Block190Part018SupportExplicit : Finset ℕ :=
  ([24341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part018 : ℚ :=
  (854825243 : ℚ) / 6636847104000000000

def SurrogateDiagonalTailChunk001Sub000Block190Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24341
    = surrogateDiagTailX0RatChunk001Sub000Block190Part018

theorem surrogateDiagonalTailChunk001Sub000Block190Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part018] using hcert

def TailChunk001Sub000Block190Part019SupportExplicit : Finset ℕ :=
  ([24342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part019 : ℚ :=
  (257205271525 : ℚ) / 2706940036656340992

def SurrogateDiagonalTailChunk001Sub000Block190Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24342
    = surrogateDiagTailX0RatChunk001Sub000Block190Part019

theorem surrogateDiagonalTailChunk001Sub000Block190Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part019] using hcert

def TailChunk001Sub000Block190Part020SupportExplicit : Finset ℕ :=
  ([24343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part020 : ℚ :=
  (5258212459 : ℚ) / 3420812738190489600

def SurrogateDiagonalTailChunk001Sub000Block190Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24343
    = surrogateDiagTailX0RatChunk001Sub000Block190Part020

theorem surrogateDiagonalTailChunk001Sub000Block190Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part020] using hcert

def TailChunk001Sub000Block190Part021SupportExplicit : Finset ℕ :=
  ([24346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part021 : ℚ :=
  (663390906625 : ℚ) / 24370991051108548608

def SurrogateDiagonalTailChunk001Sub000Block190Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24346
    = surrogateDiagTailX0RatChunk001Sub000Block190Part021

theorem surrogateDiagonalTailChunk001Sub000Block190Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part021] using hcert

def TailChunk001Sub000Block190Part022SupportExplicit : Finset ℕ :=
  ([24347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part022 : ℚ :=
  (1389471053 : ℚ) / 11061411840000000000

def SurrogateDiagonalTailChunk001Sub000Block190Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24347
    = surrogateDiagTailX0RatChunk001Sub000Block190Part022

theorem surrogateDiagonalTailChunk001Sub000Block190Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part022] using hcert

def TailChunk001Sub000Block190Part023SupportExplicit : Finset ℕ :=
  ([24349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part023 : ℚ :=
  (330281125475 : ℚ) / 318379594314525179904

def SurrogateDiagonalTailChunk001Sub000Block190Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24349
    = surrogateDiagTailX0RatChunk001Sub000Block190Part023

theorem surrogateDiagonalTailChunk001Sub000Block190Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part023] using hcert

def TailChunk001Sub000Block190Part024SupportExplicit : Finset ℕ :=
  ([24351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block190Part024 : ℚ :=
  (514683248075 : ℚ) / 21698264953913415936

def SurrogateDiagonalTailChunk001Sub000Block190Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24351
    = surrogateDiagTailX0RatChunk001Sub000Block190Part024

theorem surrogateDiagonalTailChunk001Sub000Block190Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block190Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block190Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block190Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block190Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block190Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block190Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block190HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block190Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block190Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block190Part000
    + surrogateDiagTailX0RatChunk001Sub000Block190Part001
    + surrogateDiagTailX0RatChunk001Sub000Block190Part002
    + surrogateDiagTailX0RatChunk001Sub000Block190Part003
    + surrogateDiagTailX0RatChunk001Sub000Block190Part004
    + surrogateDiagTailX0RatChunk001Sub000Block190Part005
    + surrogateDiagTailX0RatChunk001Sub000Block190Part006
    + surrogateDiagTailX0RatChunk001Sub000Block190Part007
    + surrogateDiagTailX0RatChunk001Sub000Block190Part008
    + surrogateDiagTailX0RatChunk001Sub000Block190Part009

def surrogateDiagonalTailChunk001Sub000Block190MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block190Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block190Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block190Part010
    + surrogateDiagTailX0RatChunk001Sub000Block190Part011
    + surrogateDiagTailX0RatChunk001Sub000Block190Part012
    + surrogateDiagTailX0RatChunk001Sub000Block190Part013
    + surrogateDiagTailX0RatChunk001Sub000Block190Part014
    + surrogateDiagTailX0RatChunk001Sub000Block190Part015
    + surrogateDiagTailX0RatChunk001Sub000Block190Part016
    + surrogateDiagTailX0RatChunk001Sub000Block190Part017
    + surrogateDiagTailX0RatChunk001Sub000Block190Part018
    + surrogateDiagTailX0RatChunk001Sub000Block190Part019

def surrogateDiagonalTailChunk001Sub000Block190TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block190Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block190Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block190Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block190Part020
    + surrogateDiagTailX0RatChunk001Sub000Block190Part021
    + surrogateDiagTailX0RatChunk001Sub000Block190Part022
    + surrogateDiagTailX0RatChunk001Sub000Block190Part023
    + surrogateDiagTailX0RatChunk001Sub000Block190Part024

def surrogateDiagonalTailChunk001Sub000Block190Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block190HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block190MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block190TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block190 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block190Part000
    + surrogateDiagTailX0RatChunk001Sub000Block190Part001
    + surrogateDiagTailX0RatChunk001Sub000Block190Part002
    + surrogateDiagTailX0RatChunk001Sub000Block190Part003
    + surrogateDiagTailX0RatChunk001Sub000Block190Part004
    + surrogateDiagTailX0RatChunk001Sub000Block190Part005
    + surrogateDiagTailX0RatChunk001Sub000Block190Part006
    + surrogateDiagTailX0RatChunk001Sub000Block190Part007
    + surrogateDiagTailX0RatChunk001Sub000Block190Part008
    + surrogateDiagTailX0RatChunk001Sub000Block190Part009
    + surrogateDiagTailX0RatChunk001Sub000Block190Part010
    + surrogateDiagTailX0RatChunk001Sub000Block190Part011
    + surrogateDiagTailX0RatChunk001Sub000Block190Part012
    + surrogateDiagTailX0RatChunk001Sub000Block190Part013
    + surrogateDiagTailX0RatChunk001Sub000Block190Part014
    + surrogateDiagTailX0RatChunk001Sub000Block190Part015
    + surrogateDiagTailX0RatChunk001Sub000Block190Part016
    + surrogateDiagTailX0RatChunk001Sub000Block190Part017
    + surrogateDiagTailX0RatChunk001Sub000Block190Part018
    + surrogateDiagTailX0RatChunk001Sub000Block190Part019
    + surrogateDiagTailX0RatChunk001Sub000Block190Part020
    + surrogateDiagTailX0RatChunk001Sub000Block190Part021
    + surrogateDiagTailX0RatChunk001Sub000Block190Part022
    + surrogateDiagTailX0RatChunk001Sub000Block190Part023
    + surrogateDiagTailX0RatChunk001Sub000Block190Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block190_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block190Head + surrogateDiagTailX0RatChunk001Sub000Block190Mid + surrogateDiagTailX0RatChunk001Sub000Block190Tail =
      surrogateDiagTailX0RatChunk001Sub000Block190 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block190Head surrogateDiagTailX0RatChunk001Sub000Block190Mid surrogateDiagTailX0RatChunk001Sub000Block190Tail surrogateDiagTailX0RatChunk001Sub000Block190
  ring

def SurrogateDiagonalTailChunk001Sub000Block190HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block190HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block190Head

def SurrogateDiagonalTailChunk001Sub000Block190MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block190MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block190Mid

def SurrogateDiagonalTailChunk001Sub000Block190TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block190TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block190Tail

theorem surrogateDiagonalTailChunk001Sub000Block190_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block190HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block190MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block190TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block190Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block190 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block190HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block190MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block190TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block190Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block190_eq_head_add_mid_add_tail

/-- Block 191 covers tail-support indices [14775,14800) and q from 24355 to 24395. -/

def TailChunk001Sub000Block191Part000SupportExplicit : Finset ℕ :=
  ([24355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part000 : ℚ :=
  (3956151543 : ℚ) / 960177226887034880

def SurrogateDiagonalTailChunk001Sub000Block191Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24355
    = surrogateDiagTailX0RatChunk001Sub000Block191Part000

theorem surrogateDiagonalTailChunk001Sub000Block191Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part000] using hcert

def TailChunk001Sub000Block191Part001SupportExplicit : Finset ℕ :=
  ([24357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part001 : ℚ :=
  (1977734460425 : ℚ) / 71941290342098141184

def SurrogateDiagonalTailChunk001Sub000Block191Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24357
    = surrogateDiagTailX0RatChunk001Sub000Block191Part001

theorem surrogateDiagonalTailChunk001Sub000Block191Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part001] using hcert

def TailChunk001Sub000Block191Part002SupportExplicit : Finset ℕ :=
  ([24358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part002 : ℚ :=
  (7384287427 : ℚ) / 1761557267821363200

def SurrogateDiagonalTailChunk001Sub000Block191Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24358
    = surrogateDiagTailX0RatChunk001Sub000Block191Part002

theorem surrogateDiagonalTailChunk001Sub000Block191Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part002] using hcert

def TailChunk001Sub000Block191Part003SupportExplicit : Finset ℕ :=
  ([24359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block191Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24359
    = surrogateDiagTailX0RatChunk001Sub000Block191Part003

theorem surrogateDiagonalTailChunk001Sub000Block191Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part003] using hcert

def TailChunk001Sub000Block191Part004SupportExplicit : Finset ℕ :=
  ([24361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part004 : ℚ :=
  (517347200275 : ℚ) / 689094623417774112768

def SurrogateDiagonalTailChunk001Sub000Block191Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24361
    = surrogateDiagTailX0RatChunk001Sub000Block191Part004

theorem surrogateDiagonalTailChunk001Sub000Block191Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part004] using hcert

def TailChunk001Sub000Block191Part005SupportExplicit : Finset ℕ :=
  ([24362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part005 : ℚ :=
  (30812651125 : ℚ) / 4421938809923960832

def SurrogateDiagonalTailChunk001Sub000Block191Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24362
    = surrogateDiagTailX0RatChunk001Sub000Block191Part005

theorem surrogateDiagonalTailChunk001Sub000Block191Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part005] using hcert

def TailChunk001Sub000Block191Part006SupportExplicit : Finset ℕ :=
  ([24365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part006 : ℚ :=
  (6888152077 : ℚ) / 977272983411179520

def SurrogateDiagonalTailChunk001Sub000Block191Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24365
    = surrogateDiagTailX0RatChunk001Sub000Block191Part006

theorem surrogateDiagonalTailChunk001Sub000Block191Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part006] using hcert

def TailChunk001Sub000Block191Part007SupportExplicit : Finset ℕ :=
  ([24366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part007 : ℚ :=
  (41858802103 : ℚ) / 370224590112000000

def SurrogateDiagonalTailChunk001Sub000Block191Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24366
    = surrogateDiagTailX0RatChunk001Sub000Block191Part007

theorem surrogateDiagonalTailChunk001Sub000Block191Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part007] using hcert

def TailChunk001Sub000Block191Part008SupportExplicit : Finset ℕ :=
  ([24369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part008 : ℚ :=
  (2061777617225 : ℚ) / 87050002212527797824

def SurrogateDiagonalTailChunk001Sub000Block191Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24369
    = surrogateDiagTailX0RatChunk001Sub000Block191Part008

theorem surrogateDiagonalTailChunk001Sub000Block191Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part008] using hcert

def TailChunk001Sub000Block191Part009SupportExplicit : Finset ℕ :=
  ([24370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part009 : ℚ :=
  (247621347175 : ℚ) / 7513714781073801216

def SurrogateDiagonalTailChunk001Sub000Block191Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24370
    = surrogateDiagTailX0RatChunk001Sub000Block191Part009

theorem surrogateDiagonalTailChunk001Sub000Block191Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part009] using hcert

def TailChunk001Sub000Block191Part010SupportExplicit : Finset ℕ :=
  ([24371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block191Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24371
    = surrogateDiagTailX0RatChunk001Sub000Block191Part010

theorem surrogateDiagonalTailChunk001Sub000Block191Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part010] using hcert

def TailChunk001Sub000Block191Part011SupportExplicit : Finset ℕ :=
  ([24373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block191Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24373
    = surrogateDiagTailX0RatChunk001Sub000Block191Part011

theorem surrogateDiagonalTailChunk001Sub000Block191Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part011] using hcert

def TailChunk001Sub000Block191Part012SupportExplicit : Finset ℕ :=
  ([24374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part012 : ℚ :=
  (421720411 : ℚ) / 22003668077644800

def SurrogateDiagonalTailChunk001Sub000Block191Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24374
    = surrogateDiagTailX0RatChunk001Sub000Block191Part012

theorem surrogateDiagonalTailChunk001Sub000Block191Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part012] using hcert

def TailChunk001Sub000Block191Part013SupportExplicit : Finset ℕ :=
  ([24377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part013 : ℚ :=
  (416257220725 : ℚ) / 709037132678607017088

def SurrogateDiagonalTailChunk001Sub000Block191Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24377
    = surrogateDiagTailX0RatChunk001Sub000Block191Part013

theorem surrogateDiagonalTailChunk001Sub000Block191Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part013] using hcert

def TailChunk001Sub000Block191Part014SupportExplicit : Finset ℕ :=
  ([24378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part014 : ℚ :=
  (352624037775 : ℚ) / 2804228156771270656

def SurrogateDiagonalTailChunk001Sub000Block191Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24378
    = surrogateDiagTailX0RatChunk001Sub000Block191Part014

theorem surrogateDiagonalTailChunk001Sub000Block191Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part014] using hcert

def TailChunk001Sub000Block191Part015SupportExplicit : Finset ℕ :=
  ([24379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block191Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24379
    = surrogateDiagTailX0RatChunk001Sub000Block191Part015

theorem surrogateDiagonalTailChunk001Sub000Block191Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part015] using hcert

def TailChunk001Sub000Block191Part016SupportExplicit : Finset ℕ :=
  ([24382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part016 : ℚ :=
  (6000790525 : ℚ) / 4252143873908957184

def SurrogateDiagonalTailChunk001Sub000Block191Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24382
    = surrogateDiagTailX0RatChunk001Sub000Block191Part016

theorem surrogateDiagonalTailChunk001Sub000Block191Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part016] using hcert

def TailChunk001Sub000Block191Part017SupportExplicit : Finset ℕ :=
  ([24383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part017 : ℚ :=
  (227419534675 : ℚ) / 787300335312262023168

def SurrogateDiagonalTailChunk001Sub000Block191Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24383
    = surrogateDiagTailX0RatChunk001Sub000Block191Part017

theorem surrogateDiagonalTailChunk001Sub000Block191Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part017] using hcert

def TailChunk001Sub000Block191Part018SupportExplicit : Finset ℕ :=
  ([24385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part018 : ℚ :=
  (495737192625 : ℚ) / 120614732296995045376

def SurrogateDiagonalTailChunk001Sub000Block191Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24385
    = surrogateDiagTailX0RatChunk001Sub000Block191Part018

theorem surrogateDiagonalTailChunk001Sub000Block191Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part018] using hcert

def TailChunk001Sub000Block191Part019SupportExplicit : Finset ℕ :=
  ([24386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part019 : ℚ :=
  (70350447325 : ℚ) / 51299505760043532288

def SurrogateDiagonalTailChunk001Sub000Block191Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24386
    = surrogateDiagTailX0RatChunk001Sub000Block191Part019

theorem surrogateDiagonalTailChunk001Sub000Block191Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part019] using hcert

def TailChunk001Sub000Block191Part020SupportExplicit : Finset ℕ :=
  ([24387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part020 : ℚ :=
  (50917893401 : ℚ) / 1582380875484518400

def SurrogateDiagonalTailChunk001Sub000Block191Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24387
    = surrogateDiagTailX0RatChunk001Sub000Block191Part020

theorem surrogateDiagonalTailChunk001Sub000Block191Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part020] using hcert

def TailChunk001Sub000Block191Part021SupportExplicit : Finset ℕ :=
  ([24391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block191Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24391
    = surrogateDiagTailX0RatChunk001Sub000Block191Part021

theorem surrogateDiagonalTailChunk001Sub000Block191Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part021] using hcert

def TailChunk001Sub000Block191Part022SupportExplicit : Finset ℕ :=
  ([24393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part022 : ℚ :=
  (2024032104125 : ℚ) / 78390233889106182144

def SurrogateDiagonalTailChunk001Sub000Block191Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24393
    = surrogateDiagTailX0RatChunk001Sub000Block191Part022

theorem surrogateDiagonalTailChunk001Sub000Block191Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part022] using hcert

def TailChunk001Sub000Block191Part023SupportExplicit : Finset ℕ :=
  ([24394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part023 : ℚ :=
  (2324481390625 : ℚ) / 13830456986737849632

def SurrogateDiagonalTailChunk001Sub000Block191Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24394
    = surrogateDiagTailX0RatChunk001Sub000Block191Part023

theorem surrogateDiagonalTailChunk001Sub000Block191Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part023] using hcert

def TailChunk001Sub000Block191Part024SupportExplicit : Finset ℕ :=
  ([24395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block191Part024 : ℚ :=
  (36691203341 : ℚ) / 2783695435569561600

def SurrogateDiagonalTailChunk001Sub000Block191Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24395
    = surrogateDiagTailX0RatChunk001Sub000Block191Part024

theorem surrogateDiagonalTailChunk001Sub000Block191Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block191Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block191Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block191Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block191Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block191Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block191Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block191HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block191Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block191Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block191Part000
    + surrogateDiagTailX0RatChunk001Sub000Block191Part001
    + surrogateDiagTailX0RatChunk001Sub000Block191Part002
    + surrogateDiagTailX0RatChunk001Sub000Block191Part003
    + surrogateDiagTailX0RatChunk001Sub000Block191Part004
    + surrogateDiagTailX0RatChunk001Sub000Block191Part005
    + surrogateDiagTailX0RatChunk001Sub000Block191Part006
    + surrogateDiagTailX0RatChunk001Sub000Block191Part007
    + surrogateDiagTailX0RatChunk001Sub000Block191Part008
    + surrogateDiagTailX0RatChunk001Sub000Block191Part009

def surrogateDiagonalTailChunk001Sub000Block191MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block191Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block191Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block191Part010
    + surrogateDiagTailX0RatChunk001Sub000Block191Part011
    + surrogateDiagTailX0RatChunk001Sub000Block191Part012
    + surrogateDiagTailX0RatChunk001Sub000Block191Part013
    + surrogateDiagTailX0RatChunk001Sub000Block191Part014
    + surrogateDiagTailX0RatChunk001Sub000Block191Part015
    + surrogateDiagTailX0RatChunk001Sub000Block191Part016
    + surrogateDiagTailX0RatChunk001Sub000Block191Part017
    + surrogateDiagTailX0RatChunk001Sub000Block191Part018
    + surrogateDiagTailX0RatChunk001Sub000Block191Part019

def surrogateDiagonalTailChunk001Sub000Block191TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block191Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block191Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block191Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block191Part020
    + surrogateDiagTailX0RatChunk001Sub000Block191Part021
    + surrogateDiagTailX0RatChunk001Sub000Block191Part022
    + surrogateDiagTailX0RatChunk001Sub000Block191Part023
    + surrogateDiagTailX0RatChunk001Sub000Block191Part024

def surrogateDiagonalTailChunk001Sub000Block191Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block191HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block191MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block191TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block191 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block191Part000
    + surrogateDiagTailX0RatChunk001Sub000Block191Part001
    + surrogateDiagTailX0RatChunk001Sub000Block191Part002
    + surrogateDiagTailX0RatChunk001Sub000Block191Part003
    + surrogateDiagTailX0RatChunk001Sub000Block191Part004
    + surrogateDiagTailX0RatChunk001Sub000Block191Part005
    + surrogateDiagTailX0RatChunk001Sub000Block191Part006
    + surrogateDiagTailX0RatChunk001Sub000Block191Part007
    + surrogateDiagTailX0RatChunk001Sub000Block191Part008
    + surrogateDiagTailX0RatChunk001Sub000Block191Part009
    + surrogateDiagTailX0RatChunk001Sub000Block191Part010
    + surrogateDiagTailX0RatChunk001Sub000Block191Part011
    + surrogateDiagTailX0RatChunk001Sub000Block191Part012
    + surrogateDiagTailX0RatChunk001Sub000Block191Part013
    + surrogateDiagTailX0RatChunk001Sub000Block191Part014
    + surrogateDiagTailX0RatChunk001Sub000Block191Part015
    + surrogateDiagTailX0RatChunk001Sub000Block191Part016
    + surrogateDiagTailX0RatChunk001Sub000Block191Part017
    + surrogateDiagTailX0RatChunk001Sub000Block191Part018
    + surrogateDiagTailX0RatChunk001Sub000Block191Part019
    + surrogateDiagTailX0RatChunk001Sub000Block191Part020
    + surrogateDiagTailX0RatChunk001Sub000Block191Part021
    + surrogateDiagTailX0RatChunk001Sub000Block191Part022
    + surrogateDiagTailX0RatChunk001Sub000Block191Part023
    + surrogateDiagTailX0RatChunk001Sub000Block191Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block191_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block191Head + surrogateDiagTailX0RatChunk001Sub000Block191Mid + surrogateDiagTailX0RatChunk001Sub000Block191Tail =
      surrogateDiagTailX0RatChunk001Sub000Block191 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block191Head surrogateDiagTailX0RatChunk001Sub000Block191Mid surrogateDiagTailX0RatChunk001Sub000Block191Tail surrogateDiagTailX0RatChunk001Sub000Block191
  ring

def SurrogateDiagonalTailChunk001Sub000Block191HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block191HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block191Head

def SurrogateDiagonalTailChunk001Sub000Block191MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block191MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block191Mid

def SurrogateDiagonalTailChunk001Sub000Block191TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block191TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block191Tail

theorem surrogateDiagonalTailChunk001Sub000Block191_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block191HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block191MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block191TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block191Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block191 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block191HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block191MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block191TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block191Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block191_eq_head_add_mid_add_tail

/-- Block 192 covers tail-support indices [14800,14825) and q from 24397 to 24437. -/

def TailChunk001Sub000Block192Part000SupportExplicit : Finset ℕ :=
  ([24397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part000 : ℚ :=
  (9632101783 : ℚ) / 30921606791637379200

def SurrogateDiagonalTailChunk001Sub000Block192Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24397
    = surrogateDiagTailX0RatChunk001Sub000Block192Part000

theorem surrogateDiagonalTailChunk001Sub000Block192Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part000] using hcert

def TailChunk001Sub000Block192Part001SupportExplicit : Finset ℕ :=
  ([24398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part001 : ℚ :=
  (319359247249 : ℚ) / 1507460328675379200

def SurrogateDiagonalTailChunk001Sub000Block192Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24398
    = surrogateDiagTailX0RatChunk001Sub000Block192Part001

theorem surrogateDiagonalTailChunk001Sub000Block192Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part001] using hcert

def TailChunk001Sub000Block192Part002SupportExplicit : Finset ℕ :=
  ([24401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part002 : ℚ :=
  (47383723175 : ℚ) / 45872788804562829312

def SurrogateDiagonalTailChunk001Sub000Block192Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24401
    = surrogateDiagTailX0RatChunk001Sub000Block192Part002

theorem surrogateDiagonalTailChunk001Sub000Block192Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part002] using hcert

def TailChunk001Sub000Block192Part003SupportExplicit : Finset ℕ :=
  ([24403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part003 : ℚ :=
  (5751929363 : ℚ) / 14790097565115417600

def SurrogateDiagonalTailChunk001Sub000Block192Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24403
    = surrogateDiagTailX0RatChunk001Sub000Block192Part003

theorem surrogateDiagonalTailChunk001Sub000Block192Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part003] using hcert

def TailChunk001Sub000Block192Part004SupportExplicit : Finset ℕ :=
  ([24405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part004 : ℚ :=
  (217028461525 : ℚ) / 4474546124439472128

def SurrogateDiagonalTailChunk001Sub000Block192Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24405
    = surrogateDiagTailX0RatChunk001Sub000Block192Part004

theorem surrogateDiagonalTailChunk001Sub000Block192Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part004] using hcert

def TailChunk001Sub000Block192Part005SupportExplicit : Finset ℕ :=
  ([24406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part005 : ℚ :=
  (2326768890625 : ℚ) / 13857693457338578802

def SurrogateDiagonalTailChunk001Sub000Block192Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24406
    = surrogateDiagTailX0RatChunk001Sub000Block192Part005

theorem surrogateDiagonalTailChunk001Sub000Block192Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part005] using hcert

def TailChunk001Sub000Block192Part006SupportExplicit : Finset ℕ :=
  ([24407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block192Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24407
    = surrogateDiagTailX0RatChunk001Sub000Block192Part006

theorem surrogateDiagonalTailChunk001Sub000Block192Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part006] using hcert

def TailChunk001Sub000Block192Part007SupportExplicit : Finset ℕ :=
  ([24409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part007 : ℚ :=
  (104308663 : ℚ) / 28722859142823936

def SurrogateDiagonalTailChunk001Sub000Block192Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24409
    = surrogateDiagTailX0RatChunk001Sub000Block192Part007

theorem surrogateDiagonalTailChunk001Sub000Block192Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part007] using hcert

def TailChunk001Sub000Block192Part008SupportExplicit : Finset ℕ :=
  ([24410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part008 : ℚ :=
  (253101829219 : ℚ) / 907582515983155200

def SurrogateDiagonalTailChunk001Sub000Block192Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24410
    = surrogateDiagTailX0RatChunk001Sub000Block192Part008

theorem surrogateDiagonalTailChunk001Sub000Block192Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part008] using hcert

def TailChunk001Sub000Block192Part009SupportExplicit : Finset ℕ :=
  ([24411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part009 : ℚ :=
  (2033011442675 : ℚ) / 80148600552009360384

def SurrogateDiagonalTailChunk001Sub000Block192Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24411
    = surrogateDiagTailX0RatChunk001Sub000Block192Part009

theorem surrogateDiagonalTailChunk001Sub000Block192Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part009] using hcert

def TailChunk001Sub000Block192Part010SupportExplicit : Finset ℕ :=
  ([24413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block192Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24413
    = surrogateDiagTailX0RatChunk001Sub000Block192Part010

theorem surrogateDiagonalTailChunk001Sub000Block192Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part010] using hcert

def TailChunk001Sub000Block192Part011SupportExplicit : Finset ℕ :=
  ([24414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part011 : ℚ :=
  (505198134475 : ℚ) / 873469394552881152

def SurrogateDiagonalTailChunk001Sub000Block192Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24414
    = surrogateDiagTailX0RatChunk001Sub000Block192Part011

theorem surrogateDiagonalTailChunk001Sub000Block192Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part011] using hcert

def TailChunk001Sub000Block192Part012SupportExplicit : Finset ℕ :=
  ([24415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part012 : ℚ :=
  (1607575931425 : ℚ) / 288613542759852146688

def SurrogateDiagonalTailChunk001Sub000Block192Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24415
    = surrogateDiagTailX0RatChunk001Sub000Block192Part012

theorem surrogateDiagonalTailChunk001Sub000Block192Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part012] using hcert

def TailChunk001Sub000Block192Part013SupportExplicit : Finset ℕ :=
  ([24418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part013 : ℚ :=
  (38998520999 : ℚ) / 212556126788812800

def SurrogateDiagonalTailChunk001Sub000Block192Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24418
    = surrogateDiagTailX0RatChunk001Sub000Block192Part013

theorem surrogateDiagonalTailChunk001Sub000Block192Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part013] using hcert

def TailChunk001Sub000Block192Part014SupportExplicit : Finset ℕ :=
  ([24419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block192Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24419
    = surrogateDiagTailX0RatChunk001Sub000Block192Part014

theorem surrogateDiagonalTailChunk001Sub000Block192Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part014] using hcert

def TailChunk001Sub000Block192Part015SupportExplicit : Finset ℕ :=
  ([24421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block192Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24421
    = surrogateDiagTailX0RatChunk001Sub000Block192Part015

theorem surrogateDiagonalTailChunk001Sub000Block192Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part015] using hcert

def TailChunk001Sub000Block192Part016SupportExplicit : Finset ℕ :=
  ([24422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part016 : ℚ :=
  (3727713025 : ℚ) / 22230514086584562

def SurrogateDiagonalTailChunk001Sub000Block192Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24422
    = surrogateDiagTailX0RatChunk001Sub000Block192Part016

theorem surrogateDiagonalTailChunk001Sub000Block192Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part016] using hcert

def TailChunk001Sub000Block192Part017SupportExplicit : Finset ℕ :=
  ([24423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part017 : ℚ :=
  (3632830765075 : ℚ) / 94531457789401909248

def SurrogateDiagonalTailChunk001Sub000Block192Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24423
    = surrogateDiagTailX0RatChunk001Sub000Block192Part017

theorem surrogateDiagonalTailChunk001Sub000Block192Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part017] using hcert

def TailChunk001Sub000Block192Part018SupportExplicit : Finset ℕ :=
  ([24427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part018 : ℚ :=
  (49391765525 : ℚ) / 71662455542049933312

def SurrogateDiagonalTailChunk001Sub000Block192Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24427
    = surrogateDiagTailX0RatChunk001Sub000Block192Part018

theorem surrogateDiagonalTailChunk001Sub000Block192Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part018] using hcert

def TailChunk001Sub000Block192Part019SupportExplicit : Finset ℕ :=
  ([24429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part019 : ℚ :=
  (663292540275 : ℚ) / 22813247294079500288

def SurrogateDiagonalTailChunk001Sub000Block192Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24429
    = surrogateDiagTailX0RatChunk001Sub000Block192Part019

theorem surrogateDiagonalTailChunk001Sub000Block192Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part019] using hcert

def TailChunk001Sub000Block192Part020SupportExplicit : Finset ℕ :=
  ([24430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part020 : ℚ :=
  (4957973223925 : ℚ) / 12167148300214468608

def SurrogateDiagonalTailChunk001Sub000Block192Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24430
    = surrogateDiagTailX0RatChunk001Sub000Block192Part020

theorem surrogateDiagonalTailChunk001Sub000Block192Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part020] using hcert

def TailChunk001Sub000Block192Part021SupportExplicit : Finset ℕ :=
  ([24431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part021 : ℚ :=
  (2063514997 : ℚ) / 2024498698776000000

def SurrogateDiagonalTailChunk001Sub000Block192Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24431
    = surrogateDiagTailX0RatChunk001Sub000Block192Part021

theorem surrogateDiagonalTailChunk001Sub000Block192Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part021] using hcert

def TailChunk001Sub000Block192Part022SupportExplicit : Finset ℕ :=
  ([24433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part022 : ℚ :=
  (19882159 : ℚ) / 100750727435943936

def SurrogateDiagonalTailChunk001Sub000Block192Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24433
    = surrogateDiagTailX0RatChunk001Sub000Block192Part022

theorem surrogateDiagonalTailChunk001Sub000Block192Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part022] using hcert

def TailChunk001Sub000Block192Part023SupportExplicit : Finset ℕ :=
  ([24434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part023 : ℚ :=
  (105349683175 : ℚ) / 550518569480596608

def SurrogateDiagonalTailChunk001Sub000Block192Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24434
    = surrogateDiagTailX0RatChunk001Sub000Block192Part023

theorem surrogateDiagonalTailChunk001Sub000Block192Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part023] using hcert

def TailChunk001Sub000Block192Part024SupportExplicit : Finset ℕ :=
  ([24437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block192Part024 : ℚ :=
  (30525246973 : ℚ) / 19230632104245379200

def SurrogateDiagonalTailChunk001Sub000Block192Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24437
    = surrogateDiagTailX0RatChunk001Sub000Block192Part024

theorem surrogateDiagonalTailChunk001Sub000Block192Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block192Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block192Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block192Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block192Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block192Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block192Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block192HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block192Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block192Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block192Part000
    + surrogateDiagTailX0RatChunk001Sub000Block192Part001
    + surrogateDiagTailX0RatChunk001Sub000Block192Part002
    + surrogateDiagTailX0RatChunk001Sub000Block192Part003
    + surrogateDiagTailX0RatChunk001Sub000Block192Part004
    + surrogateDiagTailX0RatChunk001Sub000Block192Part005
    + surrogateDiagTailX0RatChunk001Sub000Block192Part006
    + surrogateDiagTailX0RatChunk001Sub000Block192Part007
    + surrogateDiagTailX0RatChunk001Sub000Block192Part008
    + surrogateDiagTailX0RatChunk001Sub000Block192Part009

def surrogateDiagonalTailChunk001Sub000Block192MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block192Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block192Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block192Part010
    + surrogateDiagTailX0RatChunk001Sub000Block192Part011
    + surrogateDiagTailX0RatChunk001Sub000Block192Part012
    + surrogateDiagTailX0RatChunk001Sub000Block192Part013
    + surrogateDiagTailX0RatChunk001Sub000Block192Part014
    + surrogateDiagTailX0RatChunk001Sub000Block192Part015
    + surrogateDiagTailX0RatChunk001Sub000Block192Part016
    + surrogateDiagTailX0RatChunk001Sub000Block192Part017
    + surrogateDiagTailX0RatChunk001Sub000Block192Part018
    + surrogateDiagTailX0RatChunk001Sub000Block192Part019

def surrogateDiagonalTailChunk001Sub000Block192TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block192Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block192Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block192Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block192Part020
    + surrogateDiagTailX0RatChunk001Sub000Block192Part021
    + surrogateDiagTailX0RatChunk001Sub000Block192Part022
    + surrogateDiagTailX0RatChunk001Sub000Block192Part023
    + surrogateDiagTailX0RatChunk001Sub000Block192Part024

def surrogateDiagonalTailChunk001Sub000Block192Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block192HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block192MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block192TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block192 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block192Part000
    + surrogateDiagTailX0RatChunk001Sub000Block192Part001
    + surrogateDiagTailX0RatChunk001Sub000Block192Part002
    + surrogateDiagTailX0RatChunk001Sub000Block192Part003
    + surrogateDiagTailX0RatChunk001Sub000Block192Part004
    + surrogateDiagTailX0RatChunk001Sub000Block192Part005
    + surrogateDiagTailX0RatChunk001Sub000Block192Part006
    + surrogateDiagTailX0RatChunk001Sub000Block192Part007
    + surrogateDiagTailX0RatChunk001Sub000Block192Part008
    + surrogateDiagTailX0RatChunk001Sub000Block192Part009
    + surrogateDiagTailX0RatChunk001Sub000Block192Part010
    + surrogateDiagTailX0RatChunk001Sub000Block192Part011
    + surrogateDiagTailX0RatChunk001Sub000Block192Part012
    + surrogateDiagTailX0RatChunk001Sub000Block192Part013
    + surrogateDiagTailX0RatChunk001Sub000Block192Part014
    + surrogateDiagTailX0RatChunk001Sub000Block192Part015
    + surrogateDiagTailX0RatChunk001Sub000Block192Part016
    + surrogateDiagTailX0RatChunk001Sub000Block192Part017
    + surrogateDiagTailX0RatChunk001Sub000Block192Part018
    + surrogateDiagTailX0RatChunk001Sub000Block192Part019
    + surrogateDiagTailX0RatChunk001Sub000Block192Part020
    + surrogateDiagTailX0RatChunk001Sub000Block192Part021
    + surrogateDiagTailX0RatChunk001Sub000Block192Part022
    + surrogateDiagTailX0RatChunk001Sub000Block192Part023
    + surrogateDiagTailX0RatChunk001Sub000Block192Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block192_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block192Head + surrogateDiagTailX0RatChunk001Sub000Block192Mid + surrogateDiagTailX0RatChunk001Sub000Block192Tail =
      surrogateDiagTailX0RatChunk001Sub000Block192 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block192Head surrogateDiagTailX0RatChunk001Sub000Block192Mid surrogateDiagTailX0RatChunk001Sub000Block192Tail surrogateDiagTailX0RatChunk001Sub000Block192
  ring

def SurrogateDiagonalTailChunk001Sub000Block192HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block192HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block192Head

def SurrogateDiagonalTailChunk001Sub000Block192MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block192MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block192Mid

def SurrogateDiagonalTailChunk001Sub000Block192TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block192TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block192Tail

theorem surrogateDiagonalTailChunk001Sub000Block192_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block192HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block192MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block192TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block192Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block192 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block192HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block192MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block192TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block192Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block192_eq_head_add_mid_add_tail

/-- Block 193 covers tail-support indices [14825,14850) and q from 24438 to 24479. -/

def TailChunk001Sub000Block193Part000SupportExplicit : Finset ℕ :=
  ([24438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part000 : ℚ :=
  (4145920592725 : ℚ) / 10999625998976974848

def SurrogateDiagonalTailChunk001Sub000Block193Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24438
    = surrogateDiagTailX0RatChunk001Sub000Block193Part000

theorem surrogateDiagonalTailChunk001Sub000Block193Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part000] using hcert

def TailChunk001Sub000Block193Part001SupportExplicit : Finset ℕ :=
  ([24439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block193Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24439
    = surrogateDiagTailX0RatChunk001Sub000Block193Part001

theorem surrogateDiagonalTailChunk001Sub000Block193Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part001] using hcert

def TailChunk001Sub000Block193Part002SupportExplicit : Finset ℕ :=
  ([24441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part002 : ℚ :=
  (125025 : ℚ) / 35226347093790848

def SurrogateDiagonalTailChunk001Sub000Block193Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24441
    = surrogateDiagTailX0RatChunk001Sub000Block193Part002

theorem surrogateDiagonalTailChunk001Sub000Block193Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part002] using hcert

def TailChunk001Sub000Block193Part003SupportExplicit : Finset ℕ :=
  ([24443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block193Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24443
    = surrogateDiagTailX0RatChunk001Sub000Block193Part003

theorem surrogateDiagonalTailChunk001Sub000Block193Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part003] using hcert

def TailChunk001Sub000Block193Part004SupportExplicit : Finset ℕ :=
  ([24445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part004 : ℚ :=
  (498178192125 : ℚ) / 121806470298388135936

def SurrogateDiagonalTailChunk001Sub000Block193Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24445
    = surrogateDiagTailX0RatChunk001Sub000Block193Part004

theorem surrogateDiagonalTailChunk001Sub000Block193Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part004] using hcert

def TailChunk001Sub000Block193Part005SupportExplicit : Finset ℕ :=
  ([24446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part005 : ℚ :=
  (4223864954675 : ℚ) / 21775822649337053184

def SurrogateDiagonalTailChunk001Sub000Block193Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24446
    = surrogateDiagTailX0RatChunk001Sub000Block193Part005

theorem surrogateDiagonalTailChunk001Sub000Block193Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part005] using hcert

def TailChunk001Sub000Block193Part006SupportExplicit : Finset ℕ :=
  ([24447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part006 : ℚ :=
  (158242603 : ℚ) / 123388590607564800

def SurrogateDiagonalTailChunk001Sub000Block193Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24447
    = surrogateDiagTailX0RatChunk001Sub000Block193Part006

theorem surrogateDiagonalTailChunk001Sub000Block193Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part006] using hcert

def TailChunk001Sub000Block193Part007SupportExplicit : Finset ℕ :=
  ([24449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part007 : ℚ :=
  (359034262525 : ℚ) / 745101862787537659008

def SurrogateDiagonalTailChunk001Sub000Block193Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24449
    = surrogateDiagTailX0RatChunk001Sub000Block193Part007

theorem surrogateDiagonalTailChunk001Sub000Block193Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part007] using hcert

def TailChunk001Sub000Block193Part008SupportExplicit : Finset ℕ :=
  ([24454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part008 : ℚ :=
  (2335930140625 : ℚ) / 13967041815546760722

def SurrogateDiagonalTailChunk001Sub000Block193Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24454
    = surrogateDiagTailX0RatChunk001Sub000Block193Part008

theorem surrogateDiagonalTailChunk001Sub000Block193Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part008] using hcert

def TailChunk001Sub000Block193Part009SupportExplicit : Finset ℕ :=
  ([24455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part009 : ℚ :=
  (1583709790825 : ℚ) / 326416836970621698048

def SurrogateDiagonalTailChunk001Sub000Block193Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24455
    = surrogateDiagTailX0RatChunk001Sub000Block193Part009

theorem surrogateDiagonalTailChunk001Sub000Block193Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part009] using hcert

def TailChunk001Sub000Block193Part010SupportExplicit : Finset ℕ :=
  ([24457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part010 : ℚ :=
  (8063485189 : ℚ) / 31876644235412275200

def SurrogateDiagonalTailChunk001Sub000Block193Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24457
    = surrogateDiagTailX0RatChunk001Sub000Block193Part010

theorem surrogateDiagonalTailChunk001Sub000Block193Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part010] using hcert

def TailChunk001Sub000Block193Part011SupportExplicit : Finset ℕ :=
  ([24458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part011 : ℚ :=
  (56585430125 : ℚ) / 235287496209228921

def SurrogateDiagonalTailChunk001Sub000Block193Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24458
    = surrogateDiagTailX0RatChunk001Sub000Block193Part011

theorem surrogateDiagonalTailChunk001Sub000Block193Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part011] using hcert

def TailChunk001Sub000Block193Part012SupportExplicit : Finset ℕ :=
  ([24459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part012 : ℚ :=
  (304664617 : ℚ) / 244318868477134848

def SurrogateDiagonalTailChunk001Sub000Block193Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24459
    = surrogateDiagTailX0RatChunk001Sub000Block193Part012

theorem surrogateDiagonalTailChunk001Sub000Block193Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part012] using hcert

def TailChunk001Sub000Block193Part013SupportExplicit : Finset ℕ :=
  ([24461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part013 : ℚ :=
  (395857477 : ℚ) / 2212282368000000000

def SurrogateDiagonalTailChunk001Sub000Block193Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24461
    = surrogateDiagTailX0RatChunk001Sub000Block193Part013

theorem surrogateDiagonalTailChunk001Sub000Block193Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part013] using hcert

def TailChunk001Sub000Block193Part014SupportExplicit : Finset ℕ :=
  ([24463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part014 : ℚ :=
  (32713721775 : ℚ) / 58393040269280149504

def SurrogateDiagonalTailChunk001Sub000Block193Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24463
    = surrogateDiagTailX0RatChunk001Sub000Block193Part014

theorem surrogateDiagonalTailChunk001Sub000Block193Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part014] using hcert

def TailChunk001Sub000Block193Part015SupportExplicit : Finset ℕ :=
  ([24465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part015 : ℚ :=
  (1219564719025 : ℚ) / 38454197096974123008

def SurrogateDiagonalTailChunk001Sub000Block193Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24465
    = surrogateDiagTailX0RatChunk001Sub000Block193Part015

theorem surrogateDiagonalTailChunk001Sub000Block193Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part015] using hcert

def TailChunk001Sub000Block193Part016SupportExplicit : Finset ℕ :=
  ([24466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part016 : ℚ :=
  (54519813511 : ℚ) / 269880805944115200

def SurrogateDiagonalTailChunk001Sub000Block193Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24466
    = surrogateDiagTailX0RatChunk001Sub000Block193Part016

theorem surrogateDiagonalTailChunk001Sub000Block193Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part016] using hcert

def TailChunk001Sub000Block193Part017SupportExplicit : Finset ℕ :=
  ([24467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part017 : ℚ :=
  (1028503775 : ℚ) / 4285046697648095232

def SurrogateDiagonalTailChunk001Sub000Block193Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24467
    = surrogateDiagTailX0RatChunk001Sub000Block193Part017

theorem surrogateDiagonalTailChunk001Sub000Block193Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part017] using hcert

def TailChunk001Sub000Block193Part018SupportExplicit : Finset ℕ :=
  ([24469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block193Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24469
    = surrogateDiagTailX0RatChunk001Sub000Block193Part018

theorem surrogateDiagonalTailChunk001Sub000Block193Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part018] using hcert

def TailChunk001Sub000Block193Part019SupportExplicit : Finset ℕ :=
  ([24470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part019 : ℚ :=
  (6358696912525 : ℚ) / 22913563468690311168

def SurrogateDiagonalTailChunk001Sub000Block193Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24470
    = surrogateDiagTailX0RatChunk001Sub000Block193Part019

theorem surrogateDiagonalTailChunk001Sub000Block193Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part019] using hcert

def TailChunk001Sub000Block193Part020SupportExplicit : Finset ℕ :=
  ([24473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block193Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24473
    = surrogateDiagTailX0RatChunk001Sub000Block193Part020

theorem surrogateDiagonalTailChunk001Sub000Block193Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part020] using hcert

def TailChunk001Sub000Block193Part021SupportExplicit : Finset ℕ :=
  ([24474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part021 : ℚ :=
  (4158145592125 : ℚ) / 11064600231433016448

def SurrogateDiagonalTailChunk001Sub000Block193Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24474
    = surrogateDiagTailX0RatChunk001Sub000Block193Part021

theorem surrogateDiagonalTailChunk001Sub000Block193Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part021] using hcert

def TailChunk001Sub000Block193Part022SupportExplicit : Finset ℕ :=
  ([24477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part022 : ℚ :=
  (5795886973 : ℚ) / 6296621083538227200

def SurrogateDiagonalTailChunk001Sub000Block193Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24477
    = surrogateDiagTailX0RatChunk001Sub000Block193Part022

theorem surrogateDiagonalTailChunk001Sub000Block193Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part022] using hcert

def TailChunk001Sub000Block193Part023SupportExplicit : Finset ℕ :=
  ([24478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part023 : ℚ :=
  (2340517515625 : ℚ) / 14021958034339909842

def SurrogateDiagonalTailChunk001Sub000Block193Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24478
    = surrogateDiagTailX0RatChunk001Sub000Block193Part023

theorem surrogateDiagonalTailChunk001Sub000Block193Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part023] using hcert

def TailChunk001Sub000Block193Part024SupportExplicit : Finset ℕ :=
  ([24479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block193Part024 : ℚ :=
  (1862647331575 : ℚ) / 346653844260719689728

def SurrogateDiagonalTailChunk001Sub000Block193Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24479
    = surrogateDiagTailX0RatChunk001Sub000Block193Part024

theorem surrogateDiagonalTailChunk001Sub000Block193Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block193Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block193Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block193Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block193Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block193Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block193Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block193HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block193Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block193Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block193Part000
    + surrogateDiagTailX0RatChunk001Sub000Block193Part001
    + surrogateDiagTailX0RatChunk001Sub000Block193Part002
    + surrogateDiagTailX0RatChunk001Sub000Block193Part003
    + surrogateDiagTailX0RatChunk001Sub000Block193Part004
    + surrogateDiagTailX0RatChunk001Sub000Block193Part005
    + surrogateDiagTailX0RatChunk001Sub000Block193Part006
    + surrogateDiagTailX0RatChunk001Sub000Block193Part007
    + surrogateDiagTailX0RatChunk001Sub000Block193Part008
    + surrogateDiagTailX0RatChunk001Sub000Block193Part009

def surrogateDiagonalTailChunk001Sub000Block193MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block193Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block193Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block193Part010
    + surrogateDiagTailX0RatChunk001Sub000Block193Part011
    + surrogateDiagTailX0RatChunk001Sub000Block193Part012
    + surrogateDiagTailX0RatChunk001Sub000Block193Part013
    + surrogateDiagTailX0RatChunk001Sub000Block193Part014
    + surrogateDiagTailX0RatChunk001Sub000Block193Part015
    + surrogateDiagTailX0RatChunk001Sub000Block193Part016
    + surrogateDiagTailX0RatChunk001Sub000Block193Part017
    + surrogateDiagTailX0RatChunk001Sub000Block193Part018
    + surrogateDiagTailX0RatChunk001Sub000Block193Part019

def surrogateDiagonalTailChunk001Sub000Block193TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block193Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block193Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block193Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block193Part020
    + surrogateDiagTailX0RatChunk001Sub000Block193Part021
    + surrogateDiagTailX0RatChunk001Sub000Block193Part022
    + surrogateDiagTailX0RatChunk001Sub000Block193Part023
    + surrogateDiagTailX0RatChunk001Sub000Block193Part024

def surrogateDiagonalTailChunk001Sub000Block193Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block193HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block193MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block193TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block193 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block193Part000
    + surrogateDiagTailX0RatChunk001Sub000Block193Part001
    + surrogateDiagTailX0RatChunk001Sub000Block193Part002
    + surrogateDiagTailX0RatChunk001Sub000Block193Part003
    + surrogateDiagTailX0RatChunk001Sub000Block193Part004
    + surrogateDiagTailX0RatChunk001Sub000Block193Part005
    + surrogateDiagTailX0RatChunk001Sub000Block193Part006
    + surrogateDiagTailX0RatChunk001Sub000Block193Part007
    + surrogateDiagTailX0RatChunk001Sub000Block193Part008
    + surrogateDiagTailX0RatChunk001Sub000Block193Part009
    + surrogateDiagTailX0RatChunk001Sub000Block193Part010
    + surrogateDiagTailX0RatChunk001Sub000Block193Part011
    + surrogateDiagTailX0RatChunk001Sub000Block193Part012
    + surrogateDiagTailX0RatChunk001Sub000Block193Part013
    + surrogateDiagTailX0RatChunk001Sub000Block193Part014
    + surrogateDiagTailX0RatChunk001Sub000Block193Part015
    + surrogateDiagTailX0RatChunk001Sub000Block193Part016
    + surrogateDiagTailX0RatChunk001Sub000Block193Part017
    + surrogateDiagTailX0RatChunk001Sub000Block193Part018
    + surrogateDiagTailX0RatChunk001Sub000Block193Part019
    + surrogateDiagTailX0RatChunk001Sub000Block193Part020
    + surrogateDiagTailX0RatChunk001Sub000Block193Part021
    + surrogateDiagTailX0RatChunk001Sub000Block193Part022
    + surrogateDiagTailX0RatChunk001Sub000Block193Part023
    + surrogateDiagTailX0RatChunk001Sub000Block193Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block193_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block193Head + surrogateDiagTailX0RatChunk001Sub000Block193Mid + surrogateDiagTailX0RatChunk001Sub000Block193Tail =
      surrogateDiagTailX0RatChunk001Sub000Block193 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block193Head surrogateDiagTailX0RatChunk001Sub000Block193Mid surrogateDiagTailX0RatChunk001Sub000Block193Tail surrogateDiagTailX0RatChunk001Sub000Block193
  ring

def SurrogateDiagonalTailChunk001Sub000Block193HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block193HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block193Head

def SurrogateDiagonalTailChunk001Sub000Block193MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block193MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block193Mid

def SurrogateDiagonalTailChunk001Sub000Block193TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block193TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block193Tail

theorem surrogateDiagonalTailChunk001Sub000Block193_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block193HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block193MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block193TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block193Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block193 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block193HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block193MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block193TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block193Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block193_eq_head_add_mid_add_tail

/-- Block 194 covers tail-support indices [14850,14875) and q from 24481 to 24518. -/

def TailChunk001Sub000Block194Part000SupportExplicit : Finset ℕ :=
  ([24481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block194Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24481
    = surrogateDiagTailX0RatChunk001Sub000Block194Part000

theorem surrogateDiagonalTailChunk001Sub000Block194Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part000] using hcert

def TailChunk001Sub000Block194Part001SupportExplicit : Finset ℕ :=
  ([24482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part001 : ℚ :=
  (3746052025 : ℚ) / 22449802332413952

def SurrogateDiagonalTailChunk001Sub000Block194Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24482
    = surrogateDiagTailX0RatChunk001Sub000Block194Part001

theorem surrogateDiagonalTailChunk001Sub000Block194Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part001] using hcert

def TailChunk001Sub000Block194Part002SupportExplicit : Finset ℕ :=
  ([24483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part002 : ℚ :=
  (1667 : ℚ) / 472921826918400

def SurrogateDiagonalTailChunk001Sub000Block194Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24483
    = surrogateDiagTailX0RatChunk001Sub000Block194Part002

theorem surrogateDiagonalTailChunk001Sub000Block194Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part002] using hcert

def TailChunk001Sub000Block194Part003SupportExplicit : Finset ℕ :=
  ([24485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part003 : ℚ :=
  (264444729075 : ℚ) / 54586212003953819648

def SurrogateDiagonalTailChunk001Sub000Block194Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24485
    = surrogateDiagTailX0RatChunk001Sub000Block194Part003

theorem surrogateDiagonalTailChunk001Sub000Block194Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part003] using hcert

def TailChunk001Sub000Block194Part004SupportExplicit : Finset ℕ :=
  ([24486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part004 : ℚ :=
  (8818034059 : ℚ) / 11664922469990400

def SurrogateDiagonalTailChunk001Sub000Block194Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24486
    = surrogateDiagTailX0RatChunk001Sub000Block194Part004

theorem surrogateDiagonalTailChunk001Sub000Block194Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part004] using hcert

def TailChunk001Sub000Block194Part005SupportExplicit : Finset ℕ :=
  ([24487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part005 : ℚ :=
  (146418917 : ℚ) / 654879728333635584

def SurrogateDiagonalTailChunk001Sub000Block194Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24487
    = surrogateDiagTailX0RatChunk001Sub000Block194Part005

theorem surrogateDiagonalTailChunk001Sub000Block194Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part005] using hcert

def TailChunk001Sub000Block194Part006SupportExplicit : Finset ℕ :=
  ([24490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part006 : ℚ :=
  (237886744951 : ℚ) / 767697710056243200

def SurrogateDiagonalTailChunk001Sub000Block194Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24490
    = surrogateDiagTailX0RatChunk001Sub000Block194Part006

theorem surrogateDiagonalTailChunk001Sub000Block194Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part006] using hcert

def TailChunk001Sub000Block194Part007SupportExplicit : Finset ℕ :=
  ([24491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part007 : ℚ :=
  (420109907725 : ℚ) / 722404314984094138368

def SurrogateDiagonalTailChunk001Sub000Block194Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24491
    = surrogateDiagTailX0RatChunk001Sub000Block194Part007

theorem surrogateDiagonalTailChunk001Sub000Block194Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part007] using hcert

def TailChunk001Sub000Block194Part008SupportExplicit : Finset ℕ :=
  ([24493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part008 : ℚ :=
  (765534731075 : ℚ) / 242594575311805637184

def SurrogateDiagonalTailChunk001Sub000Block194Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24493
    = surrogateDiagTailX0RatChunk001Sub000Block194Part008

theorem surrogateDiagonalTailChunk001Sub000Block194Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part008] using hcert

def TailChunk001Sub000Block194Part009SupportExplicit : Finset ℕ :=
  ([24494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part009 : ℚ :=
  (178569325643 : ℚ) / 996145132356633600

def SurrogateDiagonalTailChunk001Sub000Block194Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24494
    = surrogateDiagTailX0RatChunk001Sub000Block194Part009

theorem surrogateDiagonalTailChunk001Sub000Block194Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part009] using hcert

def TailChunk001Sub000Block194Part010SupportExplicit : Finset ℕ :=
  ([24495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part010 : ℚ :=
  (44712762049 : ℚ) / 2304250452914995200

def SurrogateDiagonalTailChunk001Sub000Block194Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24495
    = surrogateDiagTailX0RatChunk001Sub000Block194Part010

theorem surrogateDiagonalTailChunk001Sub000Block194Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part010] using hcert

def TailChunk001Sub000Block194Part011SupportExplicit : Finset ℕ :=
  ([24497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part011 : ℚ :=
  (41892620959 : ℚ) / 18721480507392000000

def SurrogateDiagonalTailChunk001Sub000Block194Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24497
    = surrogateDiagTailX0RatChunk001Sub000Block194Part011

theorem surrogateDiagonalTailChunk001Sub000Block194Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part011] using hcert

def TailChunk001Sub000Block194Part012SupportExplicit : Finset ℕ :=
  ([24499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block194Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24499
    = surrogateDiagTailX0RatChunk001Sub000Block194Part012

theorem surrogateDiagonalTailChunk001Sub000Block194Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part012] using hcert

def TailChunk001Sub000Block194Part013SupportExplicit : Finset ℕ :=
  ([24501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part013 : ℚ :=
  (41675 : ℚ) / 11857857708813696

def SurrogateDiagonalTailChunk001Sub000Block194Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24501
    = surrogateDiagTailX0RatChunk001Sub000Block194Part013

theorem surrogateDiagonalTailChunk001Sub000Block194Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part013] using hcert

def TailChunk001Sub000Block194Part014SupportExplicit : Finset ℕ :=
  ([24502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part014 : ℚ :=
  (150087001 : ℚ) / 900930306281250

def SurrogateDiagonalTailChunk001Sub000Block194Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24502
    = surrogateDiagTailX0RatChunk001Sub000Block194Part014

theorem surrogateDiagonalTailChunk001Sub000Block194Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part014] using hcert

def TailChunk001Sub000Block194Part015SupportExplicit : Finset ℕ :=
  ([24503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part015 : ℚ :=
  (144725975 : ℚ) / 1181551104163759104

def SurrogateDiagonalTailChunk001Sub000Block194Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24503
    = surrogateDiagTailX0RatChunk001Sub000Block194Part015

theorem surrogateDiagonalTailChunk001Sub000Block194Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part015] using hcert

def TailChunk001Sub000Block194Part016SupportExplicit : Finset ℕ :=
  ([24506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part016 : ℚ :=
  (2345875140625 : ℚ) / 14086231453667902752

def SurrogateDiagonalTailChunk001Sub000Block194Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24506
    = surrogateDiagTailX0RatChunk001Sub000Block194Part016

theorem surrogateDiagonalTailChunk001Sub000Block194Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part016] using hcert

def TailChunk001Sub000Block194Part017SupportExplicit : Finset ℕ :=
  ([24509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block194Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24509
    = surrogateDiagTailX0RatChunk001Sub000Block194Part017

theorem surrogateDiagonalTailChunk001Sub000Block194Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part017] using hcert

def TailChunk001Sub000Block194Part018SupportExplicit : Finset ℕ :=
  ([24510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part018 : ℚ :=
  (203404552325 : ℚ) / 238971413925199872

def SurrogateDiagonalTailChunk001Sub000Block194Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24510
    = surrogateDiagTailX0RatChunk001Sub000Block194Part018

theorem surrogateDiagonalTailChunk001Sub000Block194Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part018] using hcert

def TailChunk001Sub000Block194Part019SupportExplicit : Finset ℕ :=
  ([24511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part019 : ℚ :=
  (6163829425 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk001Sub000Block194Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24511
    = surrogateDiagTailX0RatChunk001Sub000Block194Part019

theorem surrogateDiagonalTailChunk001Sub000Block194Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part019] using hcert

def TailChunk001Sub000Block194Part020SupportExplicit : Finset ℕ :=
  ([24513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part020 : ℚ :=
  (5001 : ℚ) / 1425733008387200

def SurrogateDiagonalTailChunk001Sub000Block194Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24513
    = surrogateDiagTailX0RatChunk001Sub000Block194Part020

theorem surrogateDiagonalTailChunk001Sub000Block194Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part020] using hcert

def TailChunk001Sub000Block194Part021SupportExplicit : Finset ℕ :=
  ([24514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part021 : ℚ :=
  (3260759690975 : ℚ) / 11494298794195943424

def SurrogateDiagonalTailChunk001Sub000Block194Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24514
    = surrogateDiagTailX0RatChunk001Sub000Block194Part021

theorem surrogateDiagonalTailChunk001Sub000Block194Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part021] using hcert

def TailChunk001Sub000Block194Part022SupportExplicit : Finset ℕ :=
  ([24515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part022 : ℚ :=
  (1503100824625 : ℚ) / 369623905773117032448

def SurrogateDiagonalTailChunk001Sub000Block194Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24515
    = surrogateDiagTailX0RatChunk001Sub000Block194Part022

theorem surrogateDiagonalTailChunk001Sub000Block194Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part022] using hcert

def TailChunk001Sub000Block194Part023SupportExplicit : Finset ℕ :=
  ([24517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block194Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24517
    = surrogateDiagTailX0RatChunk001Sub000Block194Part023

theorem surrogateDiagonalTailChunk001Sub000Block194Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part023] using hcert

def TailChunk001Sub000Block194Part024SupportExplicit : Finset ℕ :=
  ([24518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block194Part024 : ℚ :=
  (294591927139 : ℚ) / 1243777004155699200

def SurrogateDiagonalTailChunk001Sub000Block194Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24518
    = surrogateDiagTailX0RatChunk001Sub000Block194Part024

theorem surrogateDiagonalTailChunk001Sub000Block194Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block194Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block194Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block194Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block194Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block194Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block194Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block194HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block194Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block194Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block194Part000
    + surrogateDiagTailX0RatChunk001Sub000Block194Part001
    + surrogateDiagTailX0RatChunk001Sub000Block194Part002
    + surrogateDiagTailX0RatChunk001Sub000Block194Part003
    + surrogateDiagTailX0RatChunk001Sub000Block194Part004
    + surrogateDiagTailX0RatChunk001Sub000Block194Part005
    + surrogateDiagTailX0RatChunk001Sub000Block194Part006
    + surrogateDiagTailX0RatChunk001Sub000Block194Part007
    + surrogateDiagTailX0RatChunk001Sub000Block194Part008
    + surrogateDiagTailX0RatChunk001Sub000Block194Part009

def surrogateDiagonalTailChunk001Sub000Block194MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block194Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block194Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block194Part010
    + surrogateDiagTailX0RatChunk001Sub000Block194Part011
    + surrogateDiagTailX0RatChunk001Sub000Block194Part012
    + surrogateDiagTailX0RatChunk001Sub000Block194Part013
    + surrogateDiagTailX0RatChunk001Sub000Block194Part014
    + surrogateDiagTailX0RatChunk001Sub000Block194Part015
    + surrogateDiagTailX0RatChunk001Sub000Block194Part016
    + surrogateDiagTailX0RatChunk001Sub000Block194Part017
    + surrogateDiagTailX0RatChunk001Sub000Block194Part018
    + surrogateDiagTailX0RatChunk001Sub000Block194Part019

def surrogateDiagonalTailChunk001Sub000Block194TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block194Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block194Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block194Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block194Part020
    + surrogateDiagTailX0RatChunk001Sub000Block194Part021
    + surrogateDiagTailX0RatChunk001Sub000Block194Part022
    + surrogateDiagTailX0RatChunk001Sub000Block194Part023
    + surrogateDiagTailX0RatChunk001Sub000Block194Part024

def surrogateDiagonalTailChunk001Sub000Block194Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block194HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block194MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block194TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block194 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block194Part000
    + surrogateDiagTailX0RatChunk001Sub000Block194Part001
    + surrogateDiagTailX0RatChunk001Sub000Block194Part002
    + surrogateDiagTailX0RatChunk001Sub000Block194Part003
    + surrogateDiagTailX0RatChunk001Sub000Block194Part004
    + surrogateDiagTailX0RatChunk001Sub000Block194Part005
    + surrogateDiagTailX0RatChunk001Sub000Block194Part006
    + surrogateDiagTailX0RatChunk001Sub000Block194Part007
    + surrogateDiagTailX0RatChunk001Sub000Block194Part008
    + surrogateDiagTailX0RatChunk001Sub000Block194Part009
    + surrogateDiagTailX0RatChunk001Sub000Block194Part010
    + surrogateDiagTailX0RatChunk001Sub000Block194Part011
    + surrogateDiagTailX0RatChunk001Sub000Block194Part012
    + surrogateDiagTailX0RatChunk001Sub000Block194Part013
    + surrogateDiagTailX0RatChunk001Sub000Block194Part014
    + surrogateDiagTailX0RatChunk001Sub000Block194Part015
    + surrogateDiagTailX0RatChunk001Sub000Block194Part016
    + surrogateDiagTailX0RatChunk001Sub000Block194Part017
    + surrogateDiagTailX0RatChunk001Sub000Block194Part018
    + surrogateDiagTailX0RatChunk001Sub000Block194Part019
    + surrogateDiagTailX0RatChunk001Sub000Block194Part020
    + surrogateDiagTailX0RatChunk001Sub000Block194Part021
    + surrogateDiagTailX0RatChunk001Sub000Block194Part022
    + surrogateDiagTailX0RatChunk001Sub000Block194Part023
    + surrogateDiagTailX0RatChunk001Sub000Block194Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block194_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block194Head + surrogateDiagTailX0RatChunk001Sub000Block194Mid + surrogateDiagTailX0RatChunk001Sub000Block194Tail =
      surrogateDiagTailX0RatChunk001Sub000Block194 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block194Head surrogateDiagTailX0RatChunk001Sub000Block194Mid surrogateDiagTailX0RatChunk001Sub000Block194Tail surrogateDiagTailX0RatChunk001Sub000Block194
  ring

def SurrogateDiagonalTailChunk001Sub000Block194HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block194HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block194Head

def SurrogateDiagonalTailChunk001Sub000Block194MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block194MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block194Mid

def SurrogateDiagonalTailChunk001Sub000Block194TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block194TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block194Tail

theorem surrogateDiagonalTailChunk001Sub000Block194_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block194HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block194MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block194TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block194Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block194 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block194HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block194MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block194TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block194Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block194_eq_head_add_mid_add_tail

/-- Block 195 covers tail-support indices [14875,14900) and q from 24519 to 24558. -/

def TailChunk001Sub000Block195Part000SupportExplicit : Finset ℕ :=
  ([24519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part000 : ℚ :=
  (6049045281 : ℚ) / 1616967158611302400

def SurrogateDiagonalTailChunk001Sub000Block195Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24519
    = surrogateDiagTailX0RatChunk001Sub000Block195Part000

theorem surrogateDiagonalTailChunk001Sub000Block195Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part000] using hcert

def TailChunk001Sub000Block195Part001SupportExplicit : Finset ℕ :=
  ([24521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part001 : ℚ :=
  (8326761269 : ℚ) / 2065185058612838400

def SurrogateDiagonalTailChunk001Sub000Block195Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24521
    = surrogateDiagTailX0RatChunk001Sub000Block195Part001

theorem surrogateDiagonalTailChunk001Sub000Block195Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part001] using hcert

def TailChunk001Sub000Block195Part002SupportExplicit : Finset ℕ :=
  ([24522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part002 : ℚ :=
  (2960356243 : ℚ) / 7287755883724800

def SurrogateDiagonalTailChunk001Sub000Block195Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24522
    = surrogateDiagTailX0RatChunk001Sub000Block195Part002

theorem surrogateDiagonalTailChunk001Sub000Block195Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part002] using hcert

def TailChunk001Sub000Block195Part003SupportExplicit : Finset ℕ :=
  ([24523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part003 : ℚ :=
  (24556156375 : ℚ) / 214685399838847475712

def SurrogateDiagonalTailChunk001Sub000Block195Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24523
    = surrogateDiagTailX0RatChunk001Sub000Block195Part003

theorem surrogateDiagonalTailChunk001Sub000Block195Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part003] using hcert

def TailChunk001Sub000Block195Part004SupportExplicit : Finset ℕ :=
  ([24526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part004 : ℚ :=
  (2349705765625 : ℚ) / 14132276136888577842

def SurrogateDiagonalTailChunk001Sub000Block195Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24526
    = surrogateDiagTailX0RatChunk001Sub000Block195Part004

theorem surrogateDiagonalTailChunk001Sub000Block195Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part004] using hcert

def TailChunk001Sub000Block195Part005SupportExplicit : Finset ℕ :=
  ([24527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block195Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24527
    = surrogateDiagTailX0RatChunk001Sub000Block195Part005

theorem surrogateDiagonalTailChunk001Sub000Block195Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part005] using hcert

def TailChunk001Sub000Block195Part006SupportExplicit : Finset ℕ :=
  ([24529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part006 : ℚ :=
  (1872880597 : ℚ) / 3230674489680796800

def SurrogateDiagonalTailChunk001Sub000Block195Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24529
    = surrogateDiagTailX0RatChunk001Sub000Block195Part006

theorem surrogateDiagonalTailChunk001Sub000Block195Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part006] using hcert

def TailChunk001Sub000Block195Part007SupportExplicit : Finset ℕ :=
  ([24530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part007 : ℚ :=
  (14531655307 : ℚ) / 41461733350932480

def SurrogateDiagonalTailChunk001Sub000Block195Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24530
    = surrogateDiagTailX0RatChunk001Sub000Block195Part007

theorem surrogateDiagonalTailChunk001Sub000Block195Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part007] using hcert

def TailChunk001Sub000Block195Part008SupportExplicit : Finset ℕ :=
  ([24531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part008 : ℚ :=
  (709913404975 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub000Block195Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24531
    = surrogateDiagTailX0RatChunk001Sub000Block195Part008

theorem surrogateDiagonalTailChunk001Sub000Block195Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part008] using hcert

def TailChunk001Sub000Block195Part009SupportExplicit : Finset ℕ :=
  ([24533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block195Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24533
    = surrogateDiagTailX0RatChunk001Sub000Block195Part009

theorem surrogateDiagonalTailChunk001Sub000Block195Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part009] using hcert

def TailChunk001Sub000Block195Part010SupportExplicit : Finset ℕ :=
  ([24535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part010 : ℚ :=
  (4424656571 : ℚ) / 398376747417600000

def SurrogateDiagonalTailChunk001Sub000Block195Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24535
    = surrogateDiagTailX0RatChunk001Sub000Block195Part010

theorem surrogateDiagonalTailChunk001Sub000Block195Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part010] using hcert

def TailChunk001Sub000Block195Part011SupportExplicit : Finset ℕ :=
  ([24537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part011 : ℚ :=
  (41675 : ℚ) / 11927712351839616

def SurrogateDiagonalTailChunk001Sub000Block195Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24537
    = surrogateDiagTailX0RatChunk001Sub000Block195Part011

theorem surrogateDiagonalTailChunk001Sub000Block195Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part011] using hcert

def TailChunk001Sub000Block195Part012SupportExplicit : Finset ℕ :=
  ([24538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part012 : ℚ :=
  (2352005640625 : ℚ) / 14159957074269187872

def SurrogateDiagonalTailChunk001Sub000Block195Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24538
    = surrogateDiagTailX0RatChunk001Sub000Block195Part012

theorem surrogateDiagonalTailChunk001Sub000Block195Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part012] using hcert

def TailChunk001Sub000Block195Part013SupportExplicit : Finset ℕ :=
  ([24539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part013 : ℚ :=
  (704795375 : ℚ) / 3605754513015502848

def SurrogateDiagonalTailChunk001Sub000Block195Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24539
    = surrogateDiagTailX0RatChunk001Sub000Block195Part013

theorem surrogateDiagonalTailChunk001Sub000Block195Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part013] using hcert

def TailChunk001Sub000Block195Part014SupportExplicit : Finset ℕ :=
  ([24541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part014 : ℚ :=
  (1567902091 : ℚ) / 829184669437132800

def SurrogateDiagonalTailChunk001Sub000Block195Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24541
    = surrogateDiagTailX0RatChunk001Sub000Block195Part014

theorem surrogateDiagonalTailChunk001Sub000Block195Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part014] using hcert

def TailChunk001Sub000Block195Part015SupportExplicit : Finset ℕ :=
  ([24542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part015 : ℚ :=
  (1823196830875 : ℚ) / 7633228733351534592

def SurrogateDiagonalTailChunk001Sub000Block195Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24542
    = surrogateDiagTailX0RatChunk001Sub000Block195Part015

theorem surrogateDiagonalTailChunk001Sub000Block195Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part015] using hcert

def TailChunk001Sub000Block195Part016SupportExplicit : Finset ℕ :=
  ([24545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part016 : ℚ :=
  (1506779573875 : ℚ) / 371436895167277989888

def SurrogateDiagonalTailChunk001Sub000Block195Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24545
    = surrogateDiagTailX0RatChunk001Sub000Block195Part016

theorem surrogateDiagonalTailChunk001Sub000Block195Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part016] using hcert

def TailChunk001Sub000Block195Part017SupportExplicit : Finset ℕ :=
  ([24546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part017 : ℚ :=
  (167305983637 : ℚ) / 447816472761475200

def SurrogateDiagonalTailChunk001Sub000Block195Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24546
    = surrogateDiagTailX0RatChunk001Sub000Block195Part017

theorem surrogateDiagonalTailChunk001Sub000Block195Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part017] using hcert

def TailChunk001Sub000Block195Part018SupportExplicit : Finset ℕ :=
  ([24547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block195Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24547
    = surrogateDiagTailX0RatChunk001Sub000Block195Part018

theorem surrogateDiagonalTailChunk001Sub000Block195Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part018] using hcert

def TailChunk001Sub000Block195Part019SupportExplicit : Finset ℕ :=
  ([24551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block195Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24551
    = surrogateDiagTailX0RatChunk001Sub000Block195Part019

theorem surrogateDiagonalTailChunk001Sub000Block195Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part019] using hcert

def TailChunk001Sub000Block195Part020SupportExplicit : Finset ℕ :=
  ([24553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part020 : ℚ :=
  (289874663 : ℚ) / 1216801314848649600

def SurrogateDiagonalTailChunk001Sub000Block195Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24553
    = surrogateDiagTailX0RatChunk001Sub000Block195Part020

theorem surrogateDiagonalTailChunk001Sub000Block195Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part020] using hcert

def TailChunk001Sub000Block195Part021SupportExplicit : Finset ℕ :=
  ([24554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part021 : ℚ :=
  (2355073890625 : ℚ) / 14196928221900163872

def SurrogateDiagonalTailChunk001Sub000Block195Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24554
    = surrogateDiagTailX0RatChunk001Sub000Block195Part021

theorem surrogateDiagonalTailChunk001Sub000Block195Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part021] using hcert

def TailChunk001Sub000Block195Part022SupportExplicit : Finset ℕ :=
  ([24555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part022 : ℚ :=
  (251596746475 : ℚ) / 18342562724310024192

def SurrogateDiagonalTailChunk001Sub000Block195Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24555
    = surrogateDiagTailX0RatChunk001Sub000Block195Part022

theorem surrogateDiagonalTailChunk001Sub000Block195Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part022] using hcert

def TailChunk001Sub000Block195Part023SupportExplicit : Finset ℕ :=
  ([24557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part023 : ℚ :=
  (335918865275 : ℚ) / 329404711980943540224

def SurrogateDiagonalTailChunk001Sub000Block195Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24557
    = surrogateDiagTailX0RatChunk001Sub000Block195Part023

theorem surrogateDiagonalTailChunk001Sub000Block195Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part023] using hcert

def TailChunk001Sub000Block195Part024SupportExplicit : Finset ℕ :=
  ([24558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block195Part024 : ℚ :=
  (380612780975 : ℚ) / 1019756909317183488

def SurrogateDiagonalTailChunk001Sub000Block195Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24558
    = surrogateDiagTailX0RatChunk001Sub000Block195Part024

theorem surrogateDiagonalTailChunk001Sub000Block195Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block195Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block195Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block195Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block195Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block195Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block195Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block195HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block195Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block195Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block195Part000
    + surrogateDiagTailX0RatChunk001Sub000Block195Part001
    + surrogateDiagTailX0RatChunk001Sub000Block195Part002
    + surrogateDiagTailX0RatChunk001Sub000Block195Part003
    + surrogateDiagTailX0RatChunk001Sub000Block195Part004
    + surrogateDiagTailX0RatChunk001Sub000Block195Part005
    + surrogateDiagTailX0RatChunk001Sub000Block195Part006
    + surrogateDiagTailX0RatChunk001Sub000Block195Part007
    + surrogateDiagTailX0RatChunk001Sub000Block195Part008
    + surrogateDiagTailX0RatChunk001Sub000Block195Part009

def surrogateDiagonalTailChunk001Sub000Block195MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block195Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block195Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block195Part010
    + surrogateDiagTailX0RatChunk001Sub000Block195Part011
    + surrogateDiagTailX0RatChunk001Sub000Block195Part012
    + surrogateDiagTailX0RatChunk001Sub000Block195Part013
    + surrogateDiagTailX0RatChunk001Sub000Block195Part014
    + surrogateDiagTailX0RatChunk001Sub000Block195Part015
    + surrogateDiagTailX0RatChunk001Sub000Block195Part016
    + surrogateDiagTailX0RatChunk001Sub000Block195Part017
    + surrogateDiagTailX0RatChunk001Sub000Block195Part018
    + surrogateDiagTailX0RatChunk001Sub000Block195Part019

def surrogateDiagonalTailChunk001Sub000Block195TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block195Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block195Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block195Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block195Part020
    + surrogateDiagTailX0RatChunk001Sub000Block195Part021
    + surrogateDiagTailX0RatChunk001Sub000Block195Part022
    + surrogateDiagTailX0RatChunk001Sub000Block195Part023
    + surrogateDiagTailX0RatChunk001Sub000Block195Part024

def surrogateDiagonalTailChunk001Sub000Block195Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block195HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block195MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block195TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block195 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block195Part000
    + surrogateDiagTailX0RatChunk001Sub000Block195Part001
    + surrogateDiagTailX0RatChunk001Sub000Block195Part002
    + surrogateDiagTailX0RatChunk001Sub000Block195Part003
    + surrogateDiagTailX0RatChunk001Sub000Block195Part004
    + surrogateDiagTailX0RatChunk001Sub000Block195Part005
    + surrogateDiagTailX0RatChunk001Sub000Block195Part006
    + surrogateDiagTailX0RatChunk001Sub000Block195Part007
    + surrogateDiagTailX0RatChunk001Sub000Block195Part008
    + surrogateDiagTailX0RatChunk001Sub000Block195Part009
    + surrogateDiagTailX0RatChunk001Sub000Block195Part010
    + surrogateDiagTailX0RatChunk001Sub000Block195Part011
    + surrogateDiagTailX0RatChunk001Sub000Block195Part012
    + surrogateDiagTailX0RatChunk001Sub000Block195Part013
    + surrogateDiagTailX0RatChunk001Sub000Block195Part014
    + surrogateDiagTailX0RatChunk001Sub000Block195Part015
    + surrogateDiagTailX0RatChunk001Sub000Block195Part016
    + surrogateDiagTailX0RatChunk001Sub000Block195Part017
    + surrogateDiagTailX0RatChunk001Sub000Block195Part018
    + surrogateDiagTailX0RatChunk001Sub000Block195Part019
    + surrogateDiagTailX0RatChunk001Sub000Block195Part020
    + surrogateDiagTailX0RatChunk001Sub000Block195Part021
    + surrogateDiagTailX0RatChunk001Sub000Block195Part022
    + surrogateDiagTailX0RatChunk001Sub000Block195Part023
    + surrogateDiagTailX0RatChunk001Sub000Block195Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block195_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block195Head + surrogateDiagTailX0RatChunk001Sub000Block195Mid + surrogateDiagTailX0RatChunk001Sub000Block195Tail =
      surrogateDiagTailX0RatChunk001Sub000Block195 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block195Head surrogateDiagTailX0RatChunk001Sub000Block195Mid surrogateDiagTailX0RatChunk001Sub000Block195Tail surrogateDiagTailX0RatChunk001Sub000Block195
  ring

def SurrogateDiagonalTailChunk001Sub000Block195HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block195HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block195Head

def SurrogateDiagonalTailChunk001Sub000Block195MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block195MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block195Mid

def SurrogateDiagonalTailChunk001Sub000Block195TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block195TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block195Tail

theorem surrogateDiagonalTailChunk001Sub000Block195_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block195HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block195MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block195TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block195Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block195 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block195HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block195MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block195TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block195Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block195_eq_head_add_mid_add_tail

/-- Block 196 covers tail-support indices [14900,14925) and q from 24559 to 24602. -/

def TailChunk001Sub000Block196Part000SupportExplicit : Finset ℕ :=
  ([24559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part000 : ℚ :=
  (8533437421 : ℚ) / 32743986416681779200

def SurrogateDiagonalTailChunk001Sub000Block196Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24559
    = surrogateDiagTailX0RatChunk001Sub000Block196Part000

theorem surrogateDiagonalTailChunk001Sub000Block196Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part000] using hcert

def TailChunk001Sub000Block196Part001SupportExplicit : Finset ℕ :=
  ([24562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part001 : ℚ :=
  (3770574025 : ℚ) / 22744705474048512

def SurrogateDiagonalTailChunk001Sub000Block196Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24562
    = surrogateDiagTailX0RatChunk001Sub000Block196Part001

theorem surrogateDiagonalTailChunk001Sub000Block196Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part001] using hcert

def TailChunk001Sub000Block196Part002SupportExplicit : Finset ℕ :=
  ([24566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part002 : ℚ :=
  (52196975839 : ℚ) / 300258117823641600

def SurrogateDiagonalTailChunk001Sub000Block196Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24566
    = surrogateDiagTailX0RatChunk001Sub000Block196Part002

theorem surrogateDiagonalTailChunk001Sub000Block196Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part002] using hcert

def TailChunk001Sub000Block196Part003SupportExplicit : Finset ℕ :=
  ([24567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part003 : ℚ :=
  (9236971 : ℚ) / 4786184429156736

def SurrogateDiagonalTailChunk001Sub000Block196Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24567
    = surrogateDiagTailX0RatChunk001Sub000Block196Part003

theorem surrogateDiagonalTailChunk001Sub000Block196Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part003] using hcert

def TailChunk001Sub000Block196Part004SupportExplicit : Finset ℕ :=
  ([24569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part004 : ℚ :=
  (960647351 : ℚ) / 6838203673696487040

def SurrogateDiagonalTailChunk001Sub000Block196Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24569
    = surrogateDiagTailX0RatChunk001Sub000Block196Part004

theorem surrogateDiagonalTailChunk001Sub000Block196Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part004] using hcert

def TailChunk001Sub000Block196Part005SupportExplicit : Finset ℕ :=
  ([24571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block196Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24571
    = surrogateDiagTailX0RatChunk001Sub000Block196Part005

theorem surrogateDiagonalTailChunk001Sub000Block196Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part005] using hcert

def TailChunk001Sub000Block196Part006SupportExplicit : Finset ℕ :=
  ([24573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part006 : ℚ :=
  (1667 : ℚ) / 479915007062400

def SurrogateDiagonalTailChunk001Sub000Block196Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24573
    = surrogateDiagTailX0RatChunk001Sub000Block196Part006

theorem surrogateDiagonalTailChunk001Sub000Block196Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part006] using hcert

def TailChunk001Sub000Block196Part007SupportExplicit : Finset ℕ :=
  ([24574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part007 : ℚ :=
  (323985772081 : ℚ) / 1551470880065587200

def SurrogateDiagonalTailChunk001Sub000Block196Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24574
    = surrogateDiagTailX0RatChunk001Sub000Block196Part007

theorem surrogateDiagonalTailChunk001Sub000Block196Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part007] using hcert

def TailChunk001Sub000Block196Part008SupportExplicit : Finset ℕ :=
  ([24577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part008 : ℚ :=
  (2375019001 : ℚ) / 1513480972259318400

def SurrogateDiagonalTailChunk001Sub000Block196Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24577
    = surrogateDiagTailX0RatChunk001Sub000Block196Part008

theorem surrogateDiagonalTailChunk001Sub000Block196Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part008] using hcert

def TailChunk001Sub000Block196Part009SupportExplicit : Finset ℕ :=
  ([24578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part009 : ℚ :=
  (2359680015625 : ℚ) / 14252520630116155392

def SurrogateDiagonalTailChunk001Sub000Block196Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24578
    = surrogateDiagTailX0RatChunk001Sub000Block196Part009

theorem surrogateDiagonalTailChunk001Sub000Block196Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part009] using hcert

def TailChunk001Sub000Block196Part010SupportExplicit : Finset ℕ :=
  ([24581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part010 : ℚ :=
  (167354927425 : ℚ) / 831266344599686794368

def SurrogateDiagonalTailChunk001Sub000Block196Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24581
    = surrogateDiagTailX0RatChunk001Sub000Block196Part010

theorem surrogateDiagonalTailChunk001Sub000Block196Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part010] using hcert

def TailChunk001Sub000Block196Part011SupportExplicit : Finset ℕ :=
  ([24582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part011 : ℚ :=
  (76661147111 : ℚ) / 173980964723097600

def SurrogateDiagonalTailChunk001Sub000Block196Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24582
    = surrogateDiagTailX0RatChunk001Sub000Block196Part011

theorem surrogateDiagonalTailChunk001Sub000Block196Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part011] using hcert

def TailChunk001Sub000Block196Part012SupportExplicit : Finset ℕ :=
  ([24583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part012 : ℚ :=
  (831230863 : ℚ) / 483826153881600000

def SurrogateDiagonalTailChunk001Sub000Block196Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24583
    = surrogateDiagTailX0RatChunk001Sub000Block196Part012

theorem surrogateDiagonalTailChunk001Sub000Block196Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part012] using hcert

def TailChunk001Sub000Block196Part013SupportExplicit : Finset ℕ :=
  ([24585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part013 : ℚ :=
  (627438705 : ℚ) / 26207910463799296

def SurrogateDiagonalTailChunk001Sub000Block196Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24585
    = surrogateDiagTailX0RatChunk001Sub000Block196Part013

theorem surrogateDiagonalTailChunk001Sub000Block196Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part013] using hcert

def TailChunk001Sub000Block196Part014SupportExplicit : Finset ℕ :=
  ([24586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part014 : ℚ :=
  (8639919844675 : ℚ) / 45713760777539353728

def SurrogateDiagonalTailChunk001Sub000Block196Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24586
    = surrogateDiagTailX0RatChunk001Sub000Block196Part014

theorem surrogateDiagonalTailChunk001Sub000Block196Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part014] using hcert

def TailChunk001Sub000Block196Part015SupportExplicit : Finset ℕ :=
  ([24587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part015 : ℚ :=
  (363024821275 : ℚ) / 762083560009715632128

def SurrogateDiagonalTailChunk001Sub000Block196Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24587
    = surrogateDiagTailX0RatChunk001Sub000Block196Part015

theorem surrogateDiagonalTailChunk001Sub000Block196Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part015] using hcert

def TailChunk001Sub000Block196Part016SupportExplicit : Finset ℕ :=
  ([24589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part016 : ℚ :=
  (17203969925 : ℚ) / 106423357372946791056

def SurrogateDiagonalTailChunk001Sub000Block196Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24589
    = surrogateDiagTailX0RatChunk001Sub000Block196Part016

theorem surrogateDiagonalTailChunk001Sub000Block196Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part016] using hcert

def TailChunk001Sub000Block196Part017SupportExplicit : Finset ℕ :=
  ([24590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part017 : ℚ :=
  (6421228798225 : ℚ) / 23366536201051097088

def SurrogateDiagonalTailChunk001Sub000Block196Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24590
    = surrogateDiagTailX0RatChunk001Sub000Block196Part017

theorem surrogateDiagonalTailChunk001Sub000Block196Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part017] using hcert

def TailChunk001Sub000Block196Part018SupportExplicit : Finset ℕ :=
  ([24591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part018 : ℚ :=
  (147318918307 : ℚ) / 3886469657159731200

def SurrogateDiagonalTailChunk001Sub000Block196Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24591
    = surrogateDiagTailX0RatChunk001Sub000Block196Part018

theorem surrogateDiagonalTailChunk001Sub000Block196Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part018] using hcert

def TailChunk001Sub000Block196Part019SupportExplicit : Finset ℕ :=
  ([24593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block196Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24593
    = surrogateDiagTailX0RatChunk001Sub000Block196Part019

theorem surrogateDiagonalTailChunk001Sub000Block196Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part019] using hcert

def TailChunk001Sub000Block196Part020SupportExplicit : Finset ℕ :=
  ([24594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part020 : ℚ :=
  (328091610325 : ℚ) / 705203850839694408

def SurrogateDiagonalTailChunk001Sub000Block196Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24594
    = surrogateDiagTailX0RatChunk001Sub000Block196Part020

theorem surrogateDiagonalTailChunk001Sub000Block196Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part020] using hcert

def TailChunk001Sub000Block196Part021SupportExplicit : Finset ℕ :=
  ([24595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part021 : ℚ :=
  (504306940875 : ℚ) / 124824451706825906176

def SurrogateDiagonalTailChunk001Sub000Block196Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24595
    = surrogateDiagTailX0RatChunk001Sub000Block196Part021

theorem surrogateDiagonalTailChunk001Sub000Block196Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part021] using hcert

def TailChunk001Sub000Block196Part022SupportExplicit : Finset ℕ :=
  ([24599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part022 : ℚ :=
  (11024692525 : ℚ) / 19901117348976918528

def SurrogateDiagonalTailChunk001Sub000Block196Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24599
    = surrogateDiagTailX0RatChunk001Sub000Block196Part022

theorem surrogateDiagonalTailChunk001Sub000Block196Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part022] using hcert

def TailChunk001Sub000Block196Part023SupportExplicit : Finset ℕ :=
  ([24601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part023 : ℚ :=
  (127890256825 : ℚ) / 856473547507916341248

def SurrogateDiagonalTailChunk001Sub000Block196Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24601
    = surrogateDiagTailX0RatChunk001Sub000Block196Part023

theorem surrogateDiagonalTailChunk001Sub000Block196Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part023] using hcert

def TailChunk001Sub000Block196Part024SupportExplicit : Finset ℕ :=
  ([24602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block196Part024 : ℚ :=
  (151314601 : ℚ) / 915729673312800

def SurrogateDiagonalTailChunk001Sub000Block196Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24602
    = surrogateDiagTailX0RatChunk001Sub000Block196Part024

theorem surrogateDiagonalTailChunk001Sub000Block196Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block196Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block196Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block196Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block196Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block196Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block196Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block196HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block196Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block196Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block196Part000
    + surrogateDiagTailX0RatChunk001Sub000Block196Part001
    + surrogateDiagTailX0RatChunk001Sub000Block196Part002
    + surrogateDiagTailX0RatChunk001Sub000Block196Part003
    + surrogateDiagTailX0RatChunk001Sub000Block196Part004
    + surrogateDiagTailX0RatChunk001Sub000Block196Part005
    + surrogateDiagTailX0RatChunk001Sub000Block196Part006
    + surrogateDiagTailX0RatChunk001Sub000Block196Part007
    + surrogateDiagTailX0RatChunk001Sub000Block196Part008
    + surrogateDiagTailX0RatChunk001Sub000Block196Part009

def surrogateDiagonalTailChunk001Sub000Block196MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block196Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block196Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block196Part010
    + surrogateDiagTailX0RatChunk001Sub000Block196Part011
    + surrogateDiagTailX0RatChunk001Sub000Block196Part012
    + surrogateDiagTailX0RatChunk001Sub000Block196Part013
    + surrogateDiagTailX0RatChunk001Sub000Block196Part014
    + surrogateDiagTailX0RatChunk001Sub000Block196Part015
    + surrogateDiagTailX0RatChunk001Sub000Block196Part016
    + surrogateDiagTailX0RatChunk001Sub000Block196Part017
    + surrogateDiagTailX0RatChunk001Sub000Block196Part018
    + surrogateDiagTailX0RatChunk001Sub000Block196Part019

def surrogateDiagonalTailChunk001Sub000Block196TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block196Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block196Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block196Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block196Part020
    + surrogateDiagTailX0RatChunk001Sub000Block196Part021
    + surrogateDiagTailX0RatChunk001Sub000Block196Part022
    + surrogateDiagTailX0RatChunk001Sub000Block196Part023
    + surrogateDiagTailX0RatChunk001Sub000Block196Part024

def surrogateDiagonalTailChunk001Sub000Block196Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block196HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block196MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block196TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block196 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block196Part000
    + surrogateDiagTailX0RatChunk001Sub000Block196Part001
    + surrogateDiagTailX0RatChunk001Sub000Block196Part002
    + surrogateDiagTailX0RatChunk001Sub000Block196Part003
    + surrogateDiagTailX0RatChunk001Sub000Block196Part004
    + surrogateDiagTailX0RatChunk001Sub000Block196Part005
    + surrogateDiagTailX0RatChunk001Sub000Block196Part006
    + surrogateDiagTailX0RatChunk001Sub000Block196Part007
    + surrogateDiagTailX0RatChunk001Sub000Block196Part008
    + surrogateDiagTailX0RatChunk001Sub000Block196Part009
    + surrogateDiagTailX0RatChunk001Sub000Block196Part010
    + surrogateDiagTailX0RatChunk001Sub000Block196Part011
    + surrogateDiagTailX0RatChunk001Sub000Block196Part012
    + surrogateDiagTailX0RatChunk001Sub000Block196Part013
    + surrogateDiagTailX0RatChunk001Sub000Block196Part014
    + surrogateDiagTailX0RatChunk001Sub000Block196Part015
    + surrogateDiagTailX0RatChunk001Sub000Block196Part016
    + surrogateDiagTailX0RatChunk001Sub000Block196Part017
    + surrogateDiagTailX0RatChunk001Sub000Block196Part018
    + surrogateDiagTailX0RatChunk001Sub000Block196Part019
    + surrogateDiagTailX0RatChunk001Sub000Block196Part020
    + surrogateDiagTailX0RatChunk001Sub000Block196Part021
    + surrogateDiagTailX0RatChunk001Sub000Block196Part022
    + surrogateDiagTailX0RatChunk001Sub000Block196Part023
    + surrogateDiagTailX0RatChunk001Sub000Block196Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block196_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block196Head + surrogateDiagTailX0RatChunk001Sub000Block196Mid + surrogateDiagTailX0RatChunk001Sub000Block196Tail =
      surrogateDiagTailX0RatChunk001Sub000Block196 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block196Head surrogateDiagTailX0RatChunk001Sub000Block196Mid surrogateDiagTailX0RatChunk001Sub000Block196Tail surrogateDiagTailX0RatChunk001Sub000Block196
  ring

def SurrogateDiagonalTailChunk001Sub000Block196HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block196HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block196Head

def SurrogateDiagonalTailChunk001Sub000Block196MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block196MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block196Mid

def SurrogateDiagonalTailChunk001Sub000Block196TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block196TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block196Tail

theorem surrogateDiagonalTailChunk001Sub000Block196_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block196HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block196MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block196TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block196Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block196 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block196HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block196MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block196TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block196Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block196_eq_head_add_mid_add_tail

/-- Block 197 covers tail-support indices [14925,14950) and q from 24603 to 24641. -/

def TailChunk001Sub000Block197Part000SupportExplicit : Finset ℕ :=
  ([24603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part000 : ℚ :=
  (19927687825 : ℚ) / 793240383705790464

def SurrogateDiagonalTailChunk001Sub000Block197Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24603
    = surrogateDiagTailX0RatChunk001Sub000Block197Part000

theorem surrogateDiagonalTailChunk001Sub000Block197Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part000] using hcert

def TailChunk001Sub000Block197Part001SupportExplicit : Finset ℕ :=
  ([24605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part001 : ℚ :=
  (463725242425 : ℚ) / 36568896717509885952

def SurrogateDiagonalTailChunk001Sub000Block197Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24605
    = surrogateDiagTailX0RatChunk001Sub000Block197Part001

theorem surrogateDiagonalTailChunk001Sub000Block197Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part001] using hcert

def TailChunk001Sub000Block197Part002SupportExplicit : Finset ℕ :=
  ([24607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part002 : ℚ :=
  (6279647119 : ℚ) / 6250489871108620800

def SurrogateDiagonalTailChunk001Sub000Block197Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24607
    = surrogateDiagTailX0RatChunk001Sub000Block197Part002

theorem surrogateDiagonalTailChunk001Sub000Block197Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part002] using hcert

def TailChunk001Sub000Block197Part003SupportExplicit : Finset ℕ :=
  ([24609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part003 : ℚ :=
  (39022499491 : ℚ) / 1306874919903436800

def SurrogateDiagonalTailChunk001Sub000Block197Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24609
    = surrogateDiagTailX0RatChunk001Sub000Block197Part003

theorem surrogateDiagonalTailChunk001Sub000Block197Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part003] using hcert

def TailChunk001Sub000Block197Part004SupportExplicit : Finset ℕ :=
  ([24610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part004 : ℚ :=
  (5921660224225 : ℚ) / 18931324883347734528

def SurrogateDiagonalTailChunk001Sub000Block197Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24610
    = surrogateDiagTailX0RatChunk001Sub000Block197Part004

theorem surrogateDiagonalTailChunk001Sub000Block197Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part004] using hcert

def TailChunk001Sub000Block197Part005SupportExplicit : Finset ℕ :=
  ([24611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block197Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24611
    = surrogateDiagTailX0RatChunk001Sub000Block197Part005

theorem surrogateDiagonalTailChunk001Sub000Block197Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part005] using hcert

def TailChunk001Sub000Block197Part006SupportExplicit : Finset ℕ :=
  ([24613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part006 : ℚ :=
  (972651847 : ℚ) / 8718704394700500000

def SurrogateDiagonalTailChunk001Sub000Block197Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24613
    = surrogateDiagTailX0RatChunk001Sub000Block197Part006

theorem surrogateDiagonalTailChunk001Sub000Block197Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part006] using hcert

def TailChunk001Sub000Block197Part007SupportExplicit : Finset ℕ :=
  ([24614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part007 : ℚ :=
  (178979264171 : ℚ) / 996145132356633600

def SurrogateDiagonalTailChunk001Sub000Block197Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24614
    = surrogateDiagTailX0RatChunk001Sub000Block197Part007

theorem surrogateDiagonalTailChunk001Sub000Block197Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part007] using hcert

def TailChunk001Sub000Block197Part008SupportExplicit : Finset ℕ :=
  ([24617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part008 : ℚ :=
  (3001968925 : ℚ) / 25542091545217837632

def SurrogateDiagonalTailChunk001Sub000Block197Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24617
    = surrogateDiagTailX0RatChunk001Sub000Block197Part008

theorem surrogateDiagonalTailChunk001Sub000Block197Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part008] using hcert

def TailChunk001Sub000Block197Part009SupportExplicit : Finset ℕ :=
  ([24618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part009 : ℚ :=
  (11326055587 : ℚ) / 19153961482291200

def SurrogateDiagonalTailChunk001Sub000Block197Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24618
    = surrogateDiagTailX0RatChunk001Sub000Block197Part009

theorem surrogateDiagonalTailChunk001Sub000Block197Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part009] using hcert

def TailChunk001Sub000Block197Part010SupportExplicit : Finset ℕ :=
  ([24619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part010 : ℚ :=
  (774515925625 : ℚ) / 495253240688866019328

def SurrogateDiagonalTailChunk001Sub000Block197Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24619
    = surrogateDiagTailX0RatChunk001Sub000Block197Part010

theorem surrogateDiagonalTailChunk001Sub000Block197Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part010] using hcert

def TailChunk001Sub000Block197Part011SupportExplicit : Finset ℕ :=
  ([24621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part011 : ℚ :=
  (253470725 : ℚ) / 9642616295711616

def SurrogateDiagonalTailChunk001Sub000Block197Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24621
    = surrogateDiagTailX0RatChunk001Sub000Block197Part011

theorem surrogateDiagonalTailChunk001Sub000Block197Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part011] using hcert

def TailChunk001Sub000Block197Part012SupportExplicit : Finset ℕ :=
  ([24622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part012 : ℚ :=
  (8338768334575 : ℚ) / 41525645171723716608

def SurrogateDiagonalTailChunk001Sub000Block197Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24622
    = surrogateDiagTailX0RatChunk001Sub000Block197Part012

theorem surrogateDiagonalTailChunk001Sub000Block197Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part012] using hcert

def TailChunk001Sub000Block197Part013SupportExplicit : Finset ℕ :=
  ([24623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block197Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24623
    = surrogateDiagTailX0RatChunk001Sub000Block197Part013

theorem surrogateDiagonalTailChunk001Sub000Block197Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part013] using hcert

def TailChunk001Sub000Block197Part014SupportExplicit : Finset ℕ :=
  ([24626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part014 : ℚ :=
  (458925663175 : ℚ) / 1934582971440882888

def SurrogateDiagonalTailChunk001Sub000Block197Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24626
    = surrogateDiagTailX0RatChunk001Sub000Block197Part014

theorem surrogateDiagonalTailChunk001Sub000Block197Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part014] using hcert

def TailChunk001Sub000Block197Part015SupportExplicit : Finset ℕ :=
  ([24627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part015 : ℚ :=
  (1052832245575 : ℚ) / 45397949904002875392

def SurrogateDiagonalTailChunk001Sub000Block197Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24627
    = surrogateDiagTailX0RatChunk001Sub000Block197Part015

theorem surrogateDiagonalTailChunk001Sub000Block197Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part015] using hcert

def TailChunk001Sub000Block197Part016SupportExplicit : Finset ℕ :=
  ([24629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part016 : ℚ :=
  (524235823 : ℚ) / 522740250451661400

def SurrogateDiagonalTailChunk001Sub000Block197Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24629
    = surrogateDiagTailX0RatChunk001Sub000Block197Part016

theorem surrogateDiagonalTailChunk001Sub000Block197Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part016] using hcert

def TailChunk001Sub000Block197Part017SupportExplicit : Finset ℕ :=
  ([24630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part017 : ℚ :=
  (29273518049 : ℚ) / 37045222142115840

def SurrogateDiagonalTailChunk001Sub000Block197Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24630
    = surrogateDiagTailX0RatChunk001Sub000Block197Part017

theorem surrogateDiagonalTailChunk001Sub000Block197Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part017] using hcert

def TailChunk001Sub000Block197Part018SupportExplicit : Finset ℕ :=
  ([24631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block197Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24631
    = surrogateDiagTailX0RatChunk001Sub000Block197Part018

theorem surrogateDiagonalTailChunk001Sub000Block197Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part018] using hcert

def TailChunk001Sub000Block197Part019SupportExplicit : Finset ℕ :=
  ([24634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part019 : ℚ :=
  (9213374949775 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk001Sub000Block197Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24634
    = surrogateDiagTailX0RatChunk001Sub000Block197Part019

theorem surrogateDiagonalTailChunk001Sub000Block197Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part019] using hcert

def TailChunk001Sub000Block197Part020SupportExplicit : Finset ℕ :=
  ([24635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part020 : ℚ :=
  (1809941011975 : ℚ) / 270993583391176654848

def SurrogateDiagonalTailChunk001Sub000Block197Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24635
    = surrogateDiagTailX0RatChunk001Sub000Block197Part020

theorem surrogateDiagonalTailChunk001Sub000Block197Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part020] using hcert

def TailChunk001Sub000Block197Part021SupportExplicit : Finset ℕ :=
  ([24637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part021 : ℚ :=
  (534682669 : ℚ) / 3441782368335501120

def SurrogateDiagonalTailChunk001Sub000Block197Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24637
    = surrogateDiagTailX0RatChunk001Sub000Block197Part021

theorem surrogateDiagonalTailChunk001Sub000Block197Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part021] using hcert

def TailChunk001Sub000Block197Part022SupportExplicit : Finset ℕ :=
  ([24638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part022 : ℚ :=
  (68658416125 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk001Sub000Block197Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24638
    = surrogateDiagTailX0RatChunk001Sub000Block197Part022

theorem surrogateDiagonalTailChunk001Sub000Block197Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part022] using hcert

def TailChunk001Sub000Block197Part023SupportExplicit : Finset ℕ :=
  ([24639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part023 : ℚ :=
  (5890839127 : ℚ) / 231771679018790400

def SurrogateDiagonalTailChunk001Sub000Block197Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24639
    = surrogateDiagTailX0RatChunk001Sub000Block197Part023

theorem surrogateDiagonalTailChunk001Sub000Block197Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part023] using hcert

def TailChunk001Sub000Block197Part024SupportExplicit : Finset ℕ :=
  ([24641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block197Part024 : ℚ :=
  (1717452197 : ℚ) / 6636847104000000000

def SurrogateDiagonalTailChunk001Sub000Block197Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24641
    = surrogateDiagTailX0RatChunk001Sub000Block197Part024

theorem surrogateDiagonalTailChunk001Sub000Block197Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block197Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block197Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block197Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block197Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block197Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block197Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block197HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block197Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block197Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block197Part000
    + surrogateDiagTailX0RatChunk001Sub000Block197Part001
    + surrogateDiagTailX0RatChunk001Sub000Block197Part002
    + surrogateDiagTailX0RatChunk001Sub000Block197Part003
    + surrogateDiagTailX0RatChunk001Sub000Block197Part004
    + surrogateDiagTailX0RatChunk001Sub000Block197Part005
    + surrogateDiagTailX0RatChunk001Sub000Block197Part006
    + surrogateDiagTailX0RatChunk001Sub000Block197Part007
    + surrogateDiagTailX0RatChunk001Sub000Block197Part008
    + surrogateDiagTailX0RatChunk001Sub000Block197Part009

def surrogateDiagonalTailChunk001Sub000Block197MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block197Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block197Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block197Part010
    + surrogateDiagTailX0RatChunk001Sub000Block197Part011
    + surrogateDiagTailX0RatChunk001Sub000Block197Part012
    + surrogateDiagTailX0RatChunk001Sub000Block197Part013
    + surrogateDiagTailX0RatChunk001Sub000Block197Part014
    + surrogateDiagTailX0RatChunk001Sub000Block197Part015
    + surrogateDiagTailX0RatChunk001Sub000Block197Part016
    + surrogateDiagTailX0RatChunk001Sub000Block197Part017
    + surrogateDiagTailX0RatChunk001Sub000Block197Part018
    + surrogateDiagTailX0RatChunk001Sub000Block197Part019

def surrogateDiagonalTailChunk001Sub000Block197TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block197Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block197Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block197Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block197Part020
    + surrogateDiagTailX0RatChunk001Sub000Block197Part021
    + surrogateDiagTailX0RatChunk001Sub000Block197Part022
    + surrogateDiagTailX0RatChunk001Sub000Block197Part023
    + surrogateDiagTailX0RatChunk001Sub000Block197Part024

def surrogateDiagonalTailChunk001Sub000Block197Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block197HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block197MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block197TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block197 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block197Part000
    + surrogateDiagTailX0RatChunk001Sub000Block197Part001
    + surrogateDiagTailX0RatChunk001Sub000Block197Part002
    + surrogateDiagTailX0RatChunk001Sub000Block197Part003
    + surrogateDiagTailX0RatChunk001Sub000Block197Part004
    + surrogateDiagTailX0RatChunk001Sub000Block197Part005
    + surrogateDiagTailX0RatChunk001Sub000Block197Part006
    + surrogateDiagTailX0RatChunk001Sub000Block197Part007
    + surrogateDiagTailX0RatChunk001Sub000Block197Part008
    + surrogateDiagTailX0RatChunk001Sub000Block197Part009
    + surrogateDiagTailX0RatChunk001Sub000Block197Part010
    + surrogateDiagTailX0RatChunk001Sub000Block197Part011
    + surrogateDiagTailX0RatChunk001Sub000Block197Part012
    + surrogateDiagTailX0RatChunk001Sub000Block197Part013
    + surrogateDiagTailX0RatChunk001Sub000Block197Part014
    + surrogateDiagTailX0RatChunk001Sub000Block197Part015
    + surrogateDiagTailX0RatChunk001Sub000Block197Part016
    + surrogateDiagTailX0RatChunk001Sub000Block197Part017
    + surrogateDiagTailX0RatChunk001Sub000Block197Part018
    + surrogateDiagTailX0RatChunk001Sub000Block197Part019
    + surrogateDiagTailX0RatChunk001Sub000Block197Part020
    + surrogateDiagTailX0RatChunk001Sub000Block197Part021
    + surrogateDiagTailX0RatChunk001Sub000Block197Part022
    + surrogateDiagTailX0RatChunk001Sub000Block197Part023
    + surrogateDiagTailX0RatChunk001Sub000Block197Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block197_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block197Head + surrogateDiagTailX0RatChunk001Sub000Block197Mid + surrogateDiagTailX0RatChunk001Sub000Block197Tail =
      surrogateDiagTailX0RatChunk001Sub000Block197 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block197Head surrogateDiagTailX0RatChunk001Sub000Block197Mid surrogateDiagTailX0RatChunk001Sub000Block197Tail surrogateDiagTailX0RatChunk001Sub000Block197
  ring

def SurrogateDiagonalTailChunk001Sub000Block197HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block197HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block197Head

def SurrogateDiagonalTailChunk001Sub000Block197MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block197MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block197Mid

def SurrogateDiagonalTailChunk001Sub000Block197TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block197TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block197Tail

theorem surrogateDiagonalTailChunk001Sub000Block197_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block197HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block197MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block197TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block197Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block197 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block197HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block197MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block197TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block197Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block197_eq_head_add_mid_add_tail

/-- Block 198 covers tail-support indices [14950,14975) and q from 24643 to 24686. -/

def TailChunk001Sub000Block198Part000SupportExplicit : Finset ℕ :=
  ([24643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part000 : ℚ :=
  (15750918775 : ℚ) / 27426672538132414464

def SurrogateDiagonalTailChunk001Sub000Block198Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24643
    = surrogateDiagTailX0RatChunk001Sub000Block198Part000

theorem surrogateDiagonalTailChunk001Sub000Block198Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part000] using hcert

def TailChunk001Sub000Block198Part001SupportExplicit : Finset ℕ :=
  ([24645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part001 : ℚ :=
  (10458507583 : ℚ) / 186638759519846400

def SurrogateDiagonalTailChunk001Sub000Block198Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24645
    = surrogateDiagTailX0RatChunk001Sub000Block198Part001

theorem surrogateDiagonalTailChunk001Sub000Block198Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part001] using hcert

def TailChunk001Sub000Block198Part002SupportExplicit : Finset ℕ :=
  ([24646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block198Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24646
    = surrogateDiagTailX0RatChunk001Sub000Block198Part002

theorem surrogateDiagonalTailChunk001Sub000Block198Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part002] using hcert

def TailChunk001Sub000Block198Part003SupportExplicit : Finset ℕ :=
  ([24653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part003 : ℚ :=
  (12588533525 : ℚ) / 96683277949981949952

def SurrogateDiagonalTailChunk001Sub000Block198Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24653
    = surrogateDiagTailX0RatChunk001Sub000Block198Part003

theorem surrogateDiagonalTailChunk001Sub000Block198Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part003] using hcert

def TailChunk001Sub000Block198Part004SupportExplicit : Finset ℕ :=
  ([24654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part004 : ℚ :=
  (570631006475 : ℚ) / 3057118769684358144

def SurrogateDiagonalTailChunk001Sub000Block198Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24654
    = surrogateDiagTailX0RatChunk001Sub000Block198Part004

theorem surrogateDiagonalTailChunk001Sub000Block198Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part004] using hcert

def TailChunk001Sub000Block198Part005SupportExplicit : Finset ℕ :=
  ([24655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part005 : ℚ :=
  (4054151523 : ℚ) / 1008377701790382080

def SurrogateDiagonalTailChunk001Sub000Block198Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24655
    = surrogateDiagTailX0RatChunk001Sub000Block198Part005

theorem surrogateDiagonalTailChunk001Sub000Block198Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part005] using hcert

def TailChunk001Sub000Block198Part006SupportExplicit : Finset ℕ :=
  ([24657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part006 : ℚ :=
  (301542516575 : ℚ) / 13034169175299905472

def SurrogateDiagonalTailChunk001Sub000Block198Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24657
    = surrogateDiagTailX0RatChunk001Sub000Block198Part006

theorem surrogateDiagonalTailChunk001Sub000Block198Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part006] using hcert

def TailChunk001Sub000Block198Part007SupportExplicit : Finset ℕ :=
  ([24658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block198Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24658
    = surrogateDiagTailX0RatChunk001Sub000Block198Part007

theorem surrogateDiagonalTailChunk001Sub000Block198Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part007] using hcert

def TailChunk001Sub000Block198Part008SupportExplicit : Finset ℕ :=
  ([24659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block198Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24659
    = surrogateDiagTailX0RatChunk001Sub000Block198Part008

theorem surrogateDiagonalTailChunk001Sub000Block198Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part008] using hcert

def TailChunk001Sub000Block198Part009SupportExplicit : Finset ℕ :=
  ([24661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part009 : ℚ :=
  (18856053121 : ℚ) / 3571181320069324800

def SurrogateDiagonalTailChunk001Sub000Block198Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24661
    = surrogateDiagTailX0RatChunk001Sub000Block198Part009

theorem surrogateDiagonalTailChunk001Sub000Block198Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part009] using hcert

def TailChunk001Sub000Block198Part010SupportExplicit : Finset ℕ :=
  ([24662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part010 : ℚ :=
  (20485140907 : ℚ) / 1188198076192819200

def SurrogateDiagonalTailChunk001Sub000Block198Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24662
    = surrogateDiagTailX0RatChunk001Sub000Block198Part010

theorem surrogateDiagonalTailChunk001Sub000Block198Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part010] using hcert

def TailChunk001Sub000Block198Part011SupportExplicit : Finset ℕ :=
  ([24663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part011 : ℚ :=
  (2111824991 : ℚ) / 91328035525914240

def SurrogateDiagonalTailChunk001Sub000Block198Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24663
    = surrogateDiagTailX0RatChunk001Sub000Block198Part011

theorem surrogateDiagonalTailChunk001Sub000Block198Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part011] using hcert

def TailChunk001Sub000Block198Part012SupportExplicit : Finset ℕ :=
  ([24665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part012 : ℚ :=
  (1521539570875 : ℚ) / 378755628933071536128

def SurrogateDiagonalTailChunk001Sub000Block198Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24665
    = surrogateDiagTailX0RatChunk001Sub000Block198Part012

theorem surrogateDiagonalTailChunk001Sub000Block198Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part012] using hcert

def TailChunk001Sub000Block198Part013SupportExplicit : Finset ℕ :=
  ([24666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part013 : ℚ :=
  (4225525339 : ℚ) / 45664017762957120

def SurrogateDiagonalTailChunk001Sub000Block198Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24666
    = surrogateDiagTailX0RatChunk001Sub000Block198Part013

theorem surrogateDiagonalTailChunk001Sub000Block198Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part013] using hcert

def TailChunk001Sub000Block198Part014SupportExplicit : Finset ℕ :=
  ([24667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part014 : ℚ :=
  (21212336683 : ℚ) / 28976023805952000000

def SurrogateDiagonalTailChunk001Sub000Block198Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24667
    = surrogateDiagTailX0RatChunk001Sub000Block198Part014

theorem surrogateDiagonalTailChunk001Sub000Block198Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part014] using hcert

def TailChunk001Sub000Block198Part015SupportExplicit : Finset ℕ :=
  ([24670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part015 : ℚ :=
  (253747618675 : ℚ) / 7890742269438990336

def SurrogateDiagonalTailChunk001Sub000Block198Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24670
    = surrogateDiagTailX0RatChunk001Sub000Block198Part015

theorem surrogateDiagonalTailChunk001Sub000Block198Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part015] using hcert

def TailChunk001Sub000Block198Part016SupportExplicit : Finset ℕ :=
  ([24671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block198Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24671
    = surrogateDiagTailX0RatChunk001Sub000Block198Part016

theorem surrogateDiagonalTailChunk001Sub000Block198Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part016] using hcert

def TailChunk001Sub000Block198Part017SupportExplicit : Finset ℕ :=
  ([24673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part017 : ℚ :=
  (37809235723 : ℚ) / 25271398915225219200

def SurrogateDiagonalTailChunk001Sub000Block198Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24673
    = surrogateDiagTailX0RatChunk001Sub000Block198Part017

theorem surrogateDiagonalTailChunk001Sub000Block198Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part017] using hcert

def TailChunk001Sub000Block198Part018SupportExplicit : Finset ℕ :=
  ([24677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block198Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24677
    = surrogateDiagTailX0RatChunk001Sub000Block198Part018

theorem surrogateDiagonalTailChunk001Sub000Block198Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part018] using hcert

def TailChunk001Sub000Block198Part019SupportExplicit : Finset ℕ :=
  ([24679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part019 : ℚ :=
  (191614162825 : ℚ) / 151181872215752835072

def SurrogateDiagonalTailChunk001Sub000Block198Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24679
    = surrogateDiagTailX0RatChunk001Sub000Block198Part019

theorem surrogateDiagonalTailChunk001Sub000Block198Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part019] using hcert

def TailChunk001Sub000Block198Part020SupportExplicit : Finset ℕ :=
  ([24681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part020 : ℚ :=
  (253663251475 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk001Sub000Block198Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24681
    = surrogateDiagTailX0RatChunk001Sub000Block198Part020

theorem surrogateDiagonalTailChunk001Sub000Block198Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part020] using hcert

def TailChunk001Sub000Block198Part021SupportExplicit : Finset ℕ :=
  ([24682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part021 : ℚ :=
  (2706098251 : ℚ) / 103259252930641920

def SurrogateDiagonalTailChunk001Sub000Block198Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24682
    = surrogateDiagTailX0RatChunk001Sub000Block198Part021

theorem surrogateDiagonalTailChunk001Sub000Block198Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part021] using hcert

def TailChunk001Sub000Block198Part022SupportExplicit : Finset ℕ :=
  ([24683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block198Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24683
    = surrogateDiagTailX0RatChunk001Sub000Block198Part022

theorem surrogateDiagonalTailChunk001Sub000Block198Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part022] using hcert

def TailChunk001Sub000Block198Part023SupportExplicit : Finset ℕ :=
  ([24685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part023 : ℚ :=
  (508002190125 : ℚ) / 126661951089492361216

def SurrogateDiagonalTailChunk001Sub000Block198Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24685
    = surrogateDiagTailX0RatChunk001Sub000Block198Part023

theorem surrogateDiagonalTailChunk001Sub000Block198Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part023] using hcert

def TailChunk001Sub000Block198Part024SupportExplicit : Finset ℕ :=
  ([24686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block198Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block198Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24686
    = surrogateDiagTailX0RatChunk001Sub000Block198Part024

theorem surrogateDiagonalTailChunk001Sub000Block198Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block198Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block198Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block198Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block198Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block198Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block198Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block198HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block198Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block198Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block198Part000
    + surrogateDiagTailX0RatChunk001Sub000Block198Part001
    + surrogateDiagTailX0RatChunk001Sub000Block198Part002
    + surrogateDiagTailX0RatChunk001Sub000Block198Part003
    + surrogateDiagTailX0RatChunk001Sub000Block198Part004
    + surrogateDiagTailX0RatChunk001Sub000Block198Part005
    + surrogateDiagTailX0RatChunk001Sub000Block198Part006
    + surrogateDiagTailX0RatChunk001Sub000Block198Part007
    + surrogateDiagTailX0RatChunk001Sub000Block198Part008
    + surrogateDiagTailX0RatChunk001Sub000Block198Part009

def surrogateDiagonalTailChunk001Sub000Block198MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block198Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block198Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block198Part010
    + surrogateDiagTailX0RatChunk001Sub000Block198Part011
    + surrogateDiagTailX0RatChunk001Sub000Block198Part012
    + surrogateDiagTailX0RatChunk001Sub000Block198Part013
    + surrogateDiagTailX0RatChunk001Sub000Block198Part014
    + surrogateDiagTailX0RatChunk001Sub000Block198Part015
    + surrogateDiagTailX0RatChunk001Sub000Block198Part016
    + surrogateDiagTailX0RatChunk001Sub000Block198Part017
    + surrogateDiagTailX0RatChunk001Sub000Block198Part018
    + surrogateDiagTailX0RatChunk001Sub000Block198Part019

def surrogateDiagonalTailChunk001Sub000Block198TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block198Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block198Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block198Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block198Part020
    + surrogateDiagTailX0RatChunk001Sub000Block198Part021
    + surrogateDiagTailX0RatChunk001Sub000Block198Part022
    + surrogateDiagTailX0RatChunk001Sub000Block198Part023
    + surrogateDiagTailX0RatChunk001Sub000Block198Part024

def surrogateDiagonalTailChunk001Sub000Block198Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block198HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block198MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block198TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block198 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block198Part000
    + surrogateDiagTailX0RatChunk001Sub000Block198Part001
    + surrogateDiagTailX0RatChunk001Sub000Block198Part002
    + surrogateDiagTailX0RatChunk001Sub000Block198Part003
    + surrogateDiagTailX0RatChunk001Sub000Block198Part004
    + surrogateDiagTailX0RatChunk001Sub000Block198Part005
    + surrogateDiagTailX0RatChunk001Sub000Block198Part006
    + surrogateDiagTailX0RatChunk001Sub000Block198Part007
    + surrogateDiagTailX0RatChunk001Sub000Block198Part008
    + surrogateDiagTailX0RatChunk001Sub000Block198Part009
    + surrogateDiagTailX0RatChunk001Sub000Block198Part010
    + surrogateDiagTailX0RatChunk001Sub000Block198Part011
    + surrogateDiagTailX0RatChunk001Sub000Block198Part012
    + surrogateDiagTailX0RatChunk001Sub000Block198Part013
    + surrogateDiagTailX0RatChunk001Sub000Block198Part014
    + surrogateDiagTailX0RatChunk001Sub000Block198Part015
    + surrogateDiagTailX0RatChunk001Sub000Block198Part016
    + surrogateDiagTailX0RatChunk001Sub000Block198Part017
    + surrogateDiagTailX0RatChunk001Sub000Block198Part018
    + surrogateDiagTailX0RatChunk001Sub000Block198Part019
    + surrogateDiagTailX0RatChunk001Sub000Block198Part020
    + surrogateDiagTailX0RatChunk001Sub000Block198Part021
    + surrogateDiagTailX0RatChunk001Sub000Block198Part022
    + surrogateDiagTailX0RatChunk001Sub000Block198Part023
    + surrogateDiagTailX0RatChunk001Sub000Block198Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block198_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block198Head + surrogateDiagTailX0RatChunk001Sub000Block198Mid + surrogateDiagTailX0RatChunk001Sub000Block198Tail =
      surrogateDiagTailX0RatChunk001Sub000Block198 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block198Head surrogateDiagTailX0RatChunk001Sub000Block198Mid surrogateDiagTailX0RatChunk001Sub000Block198Tail surrogateDiagTailX0RatChunk001Sub000Block198
  ring

def SurrogateDiagonalTailChunk001Sub000Block198HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block198HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block198Head

def SurrogateDiagonalTailChunk001Sub000Block198MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block198MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block198Mid

def SurrogateDiagonalTailChunk001Sub000Block198TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block198TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block198Tail

theorem surrogateDiagonalTailChunk001Sub000Block198_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block198HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block198MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block198TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block198Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block198 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block198HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block198MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block198TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block198Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block198_eq_head_add_mid_add_tail

/-- Block 199 covers tail-support indices [14975,15000) and q from 24689 to 24726. -/

def TailChunk001Sub000Block199Part000SupportExplicit : Finset ℕ :=
  ([24689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part000 : ℚ :=
  (777824273375 : ℚ) / 250455801828117916224

def SurrogateDiagonalTailChunk001Sub000Block199Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24689
    = surrogateDiagTailX0RatChunk001Sub000Block199Part000

theorem surrogateDiagonalTailChunk001Sub000Block199Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part000] using hcert

def TailChunk001Sub000Block199Part001SupportExplicit : Finset ℕ :=
  ([24690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part001 : ℚ :=
  (1142733092725 : ℚ) / 4675995418926809088

def SurrogateDiagonalTailChunk001Sub000Block199Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24690
    = surrogateDiagTailX0RatChunk001Sub000Block199Part001

theorem surrogateDiagonalTailChunk001Sub000Block199Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part001] using hcert

def TailChunk001Sub000Block199Part002SupportExplicit : Finset ℕ :=
  ([24691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block199Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24691
    = surrogateDiagTailX0RatChunk001Sub000Block199Part002

theorem surrogateDiagonalTailChunk001Sub000Block199Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part002] using hcert

def TailChunk001Sub000Block199Part003SupportExplicit : Finset ℕ :=
  ([24693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part003 : ℚ :=
  (16935724927 : ℚ) / 734186126649357120

def SurrogateDiagonalTailChunk001Sub000Block199Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24693
    = surrogateDiagTailX0RatChunk001Sub000Block199Part003

theorem surrogateDiagonalTailChunk001Sub000Block199Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part003] using hcert

def TailChunk001Sub000Block199Part004SupportExplicit : Finset ℕ :=
  ([24694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block199Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24694
    = surrogateDiagTailX0RatChunk001Sub000Block199Part004

theorem surrogateDiagonalTailChunk001Sub000Block199Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part004] using hcert

def TailChunk001Sub000Block199Part005SupportExplicit : Finset ℕ :=
  ([24695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part005 : ℚ :=
  (7075062721 : ℚ) / 1031427892099153920

def SurrogateDiagonalTailChunk001Sub000Block199Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24695
    = surrogateDiagTailX0RatChunk001Sub000Block199Part005

theorem surrogateDiagonalTailChunk001Sub000Block199Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part005] using hcert

def TailChunk001Sub000Block199Part006SupportExplicit : Finset ℕ :=
  ([24697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block199Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24697
    = surrogateDiagTailX0RatChunk001Sub000Block199Part006

theorem surrogateDiagonalTailChunk001Sub000Block199Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part006] using hcert

def TailChunk001Sub000Block199Part007SupportExplicit : Finset ℕ :=
  ([24698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part007 : ℚ :=
  (15008917275 : ℚ) / 8827564969832480768

def SurrogateDiagonalTailChunk001Sub000Block199Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24698
    = surrogateDiagTailX0RatChunk001Sub000Block199Part007

theorem surrogateDiagonalTailChunk001Sub000Block199Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part007] using hcert

def TailChunk001Sub000Block199Part008SupportExplicit : Finset ℕ :=
  ([24699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part008 : ℚ :=
  (151285320775 : ℚ) / 6561607633970651136

def SurrogateDiagonalTailChunk001Sub000Block199Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24699
    = surrogateDiagTailX0RatChunk001Sub000Block199Part008

theorem surrogateDiagonalTailChunk001Sub000Block199Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part008] using hcert

def TailChunk001Sub000Block199Part009SupportExplicit : Finset ℕ :=
  ([24701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part009 : ℚ :=
  (694701175 : ℚ) / 1264592994294693888

def SurrogateDiagonalTailChunk001Sub000Block199Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24701
    = surrogateDiagTailX0RatChunk001Sub000Block199Part009

theorem surrogateDiagonalTailChunk001Sub000Block199Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part009] using hcert

def TailChunk001Sub000Block199Part010SupportExplicit : Finset ℕ :=
  ([24702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part010 : ℚ :=
  (359687134875 : ℚ) / 3136146337488541696

def SurrogateDiagonalTailChunk001Sub000Block199Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24702
    = surrogateDiagTailX0RatChunk001Sub000Block199Part010

theorem surrogateDiagonalTailChunk001Sub000Block199Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part010] using hcert

def TailChunk001Sub000Block199Part011SupportExplicit : Finset ℕ :=
  ([24703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part011 : ℚ :=
  (778705847075 : ℚ) / 251024534615052140544

def SurrogateDiagonalTailChunk001Sub000Block199Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24703
    = surrogateDiagTailX0RatChunk001Sub000Block199Part011

theorem surrogateDiagonalTailChunk001Sub000Block199Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part011] using hcert

def TailChunk001Sub000Block199Part012SupportExplicit : Finset ℕ :=
  ([24706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part012 : ℚ :=
  (12706380781 : ℚ) / 1585105883241091200

def SurrogateDiagonalTailChunk001Sub000Block199Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24706
    = surrogateDiagTailX0RatChunk001Sub000Block199Part012

theorem surrogateDiagonalTailChunk001Sub000Block199Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part012] using hcert

def TailChunk001Sub000Block199Part013SupportExplicit : Finset ℕ :=
  ([24707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part013 : ℚ :=
  (9869164723 : ℚ) / 32525511873550387200

def SurrogateDiagonalTailChunk001Sub000Block199Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24707
    = surrogateDiagTailX0RatChunk001Sub000Block199Part013

theorem surrogateDiagonalTailChunk001Sub000Block199Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part013] using hcert

def TailChunk001Sub000Block199Part014SupportExplicit : Finset ℕ :=
  ([24709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block199Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24709
    = surrogateDiagTailX0RatChunk001Sub000Block199Part014

theorem surrogateDiagonalTailChunk001Sub000Block199Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part014] using hcert

def TailChunk001Sub000Block199Part015SupportExplicit : Finset ℕ :=
  ([24710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part015 : ℚ :=
  (55906857475 : ℚ) / 707570917919686656

def SurrogateDiagonalTailChunk001Sub000Block199Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24710
    = surrogateDiagTailX0RatChunk001Sub000Block199Part015

theorem surrogateDiagonalTailChunk001Sub000Block199Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part015] using hcert

def TailChunk001Sub000Block199Part016SupportExplicit : Finset ℕ :=
  ([24711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part016 : ℚ :=
  (132503311925 : ℚ) / 5752574012541079104

def SurrogateDiagonalTailChunk001Sub000Block199Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24711
    = surrogateDiagTailX0RatChunk001Sub000Block199Part016

theorem surrogateDiagonalTailChunk001Sub000Block199Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part016] using hcert

def TailChunk001Sub000Block199Part017SupportExplicit : Finset ℕ :=
  ([24713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part017 : ℚ :=
  (18196532209 : ℚ) / 27028767232512000000

def SurrogateDiagonalTailChunk001Sub000Block199Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24713
    = surrogateDiagTailX0RatChunk001Sub000Block199Part017

theorem surrogateDiagonalTailChunk001Sub000Block199Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part017] using hcert

def TailChunk001Sub000Block199Part018SupportExplicit : Finset ℕ :=
  ([24715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part018 : ℚ :=
  (509236939875 : ℚ) / 127278935299906410496

def SurrogateDiagonalTailChunk001Sub000Block199Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24715
    = surrogateDiagTailX0RatChunk001Sub000Block199Part018

theorem surrogateDiagonalTailChunk001Sub000Block199Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part018] using hcert

def TailChunk001Sub000Block199Part019SupportExplicit : Finset ℕ :=
  ([24717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part019 : ℚ :=
  (5794423393 : ℚ) / 104735831948034048

def SurrogateDiagonalTailChunk001Sub000Block199Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24717
    = surrogateDiagTailX0RatChunk001Sub000Block199Part019

theorem surrogateDiagonalTailChunk001Sub000Block199Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part019] using hcert

def TailChunk001Sub000Block199Part020SupportExplicit : Finset ℕ :=
  ([24718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part020 : ℚ :=
  (117658638125 : ℚ) / 22762673897304489984

def SurrogateDiagonalTailChunk001Sub000Block199Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24718
    = surrogateDiagTailX0RatChunk001Sub000Block199Part020

theorem surrogateDiagonalTailChunk001Sub000Block199Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part020] using hcert

def TailChunk001Sub000Block199Part021SupportExplicit : Finset ℕ :=
  ([24719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part021 : ℚ :=
  (17114769973 : ℚ) / 29988191799072000000

def SurrogateDiagonalTailChunk001Sub000Block199Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24719
    = surrogateDiagTailX0RatChunk001Sub000Block199Part021

theorem surrogateDiagonalTailChunk001Sub000Block199Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part021] using hcert

def TailChunk001Sub000Block199Part022SupportExplicit : Finset ℕ :=
  ([24721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part022 : ℚ :=
  (37233205525 : ℚ) / 215965296004691034912

def SurrogateDiagonalTailChunk001Sub000Block199Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24721
    = surrogateDiagTailX0RatChunk001Sub000Block199Part022

theorem surrogateDiagonalTailChunk001Sub000Block199Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part022] using hcert

def TailChunk001Sub000Block199Part023SupportExplicit : Finset ℕ :=
  ([24722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part023 : ℚ :=
  (47773705775 : ℚ) / 26377483207372643904

def SurrogateDiagonalTailChunk001Sub000Block199Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24722
    = surrogateDiagTailX0RatChunk001Sub000Block199Part023

theorem surrogateDiagonalTailChunk001Sub000Block199Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part023] using hcert

def TailChunk001Sub000Block199Part024SupportExplicit : Finset ℕ :=
  ([24726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block199Part024 : ℚ :=
  (556042673375 : ℚ) / 4136091716566646784

def SurrogateDiagonalTailChunk001Sub000Block199Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24726
    = surrogateDiagTailX0RatChunk001Sub000Block199Part024

theorem surrogateDiagonalTailChunk001Sub000Block199Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block199Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block199Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block199Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block199Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block199Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block199Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block199HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block199Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block199Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block199Part000
    + surrogateDiagTailX0RatChunk001Sub000Block199Part001
    + surrogateDiagTailX0RatChunk001Sub000Block199Part002
    + surrogateDiagTailX0RatChunk001Sub000Block199Part003
    + surrogateDiagTailX0RatChunk001Sub000Block199Part004
    + surrogateDiagTailX0RatChunk001Sub000Block199Part005
    + surrogateDiagTailX0RatChunk001Sub000Block199Part006
    + surrogateDiagTailX0RatChunk001Sub000Block199Part007
    + surrogateDiagTailX0RatChunk001Sub000Block199Part008
    + surrogateDiagTailX0RatChunk001Sub000Block199Part009

def surrogateDiagonalTailChunk001Sub000Block199MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block199Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block199Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block199Part010
    + surrogateDiagTailX0RatChunk001Sub000Block199Part011
    + surrogateDiagTailX0RatChunk001Sub000Block199Part012
    + surrogateDiagTailX0RatChunk001Sub000Block199Part013
    + surrogateDiagTailX0RatChunk001Sub000Block199Part014
    + surrogateDiagTailX0RatChunk001Sub000Block199Part015
    + surrogateDiagTailX0RatChunk001Sub000Block199Part016
    + surrogateDiagTailX0RatChunk001Sub000Block199Part017
    + surrogateDiagTailX0RatChunk001Sub000Block199Part018
    + surrogateDiagTailX0RatChunk001Sub000Block199Part019

def surrogateDiagonalTailChunk001Sub000Block199TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block199Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block199Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block199Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block199Part020
    + surrogateDiagTailX0RatChunk001Sub000Block199Part021
    + surrogateDiagTailX0RatChunk001Sub000Block199Part022
    + surrogateDiagTailX0RatChunk001Sub000Block199Part023
    + surrogateDiagTailX0RatChunk001Sub000Block199Part024

def surrogateDiagonalTailChunk001Sub000Block199Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block199HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block199MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block199TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block199 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block199Part000
    + surrogateDiagTailX0RatChunk001Sub000Block199Part001
    + surrogateDiagTailX0RatChunk001Sub000Block199Part002
    + surrogateDiagTailX0RatChunk001Sub000Block199Part003
    + surrogateDiagTailX0RatChunk001Sub000Block199Part004
    + surrogateDiagTailX0RatChunk001Sub000Block199Part005
    + surrogateDiagTailX0RatChunk001Sub000Block199Part006
    + surrogateDiagTailX0RatChunk001Sub000Block199Part007
    + surrogateDiagTailX0RatChunk001Sub000Block199Part008
    + surrogateDiagTailX0RatChunk001Sub000Block199Part009
    + surrogateDiagTailX0RatChunk001Sub000Block199Part010
    + surrogateDiagTailX0RatChunk001Sub000Block199Part011
    + surrogateDiagTailX0RatChunk001Sub000Block199Part012
    + surrogateDiagTailX0RatChunk001Sub000Block199Part013
    + surrogateDiagTailX0RatChunk001Sub000Block199Part014
    + surrogateDiagTailX0RatChunk001Sub000Block199Part015
    + surrogateDiagTailX0RatChunk001Sub000Block199Part016
    + surrogateDiagTailX0RatChunk001Sub000Block199Part017
    + surrogateDiagTailX0RatChunk001Sub000Block199Part018
    + surrogateDiagTailX0RatChunk001Sub000Block199Part019
    + surrogateDiagTailX0RatChunk001Sub000Block199Part020
    + surrogateDiagTailX0RatChunk001Sub000Block199Part021
    + surrogateDiagTailX0RatChunk001Sub000Block199Part022
    + surrogateDiagTailX0RatChunk001Sub000Block199Part023
    + surrogateDiagTailX0RatChunk001Sub000Block199Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block199_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block199Head + surrogateDiagTailX0RatChunk001Sub000Block199Mid + surrogateDiagTailX0RatChunk001Sub000Block199Tail =
      surrogateDiagTailX0RatChunk001Sub000Block199 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block199Head surrogateDiagTailX0RatChunk001Sub000Block199Mid surrogateDiagTailX0RatChunk001Sub000Block199Tail surrogateDiagTailX0RatChunk001Sub000Block199
  ring

def SurrogateDiagonalTailChunk001Sub000Block199HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block199HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block199Head

def SurrogateDiagonalTailChunk001Sub000Block199MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block199MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block199Mid

def SurrogateDiagonalTailChunk001Sub000Block199TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block199TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block199Tail

theorem surrogateDiagonalTailChunk001Sub000Block199_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block199HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block199MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block199TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block199Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block199 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block199HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block199MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block199TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block199Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block199_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
