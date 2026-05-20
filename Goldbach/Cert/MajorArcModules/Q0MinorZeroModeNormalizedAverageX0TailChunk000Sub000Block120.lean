import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [120,121). -/

/- Block 120 covers tail-support indices [3000,3025) and q from 4982 to 5019. -/

def TailChunk000Sub000Block120Part000SupportExplicit : Finset ℕ :=
  ([4982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part000 : ℚ :=
  (745128106375 : ℚ) / 81859966041704448

def SurrogateDiagonalTailChunk000Sub000Block120Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4982
    = surrogateDiagTailX0RatChunk000Sub000Block120Part000

theorem surrogateDiagonalTailChunk000Sub000Block120Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part000] using hcert

def TailChunk000Sub000Block120Part001SupportExplicit : Finset ℕ :=
  ([4983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part001 : ℚ :=
  (7476260441 : ℚ) / 1620324000000000

def SurrogateDiagonalTailChunk000Sub000Block120Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4983
    = surrogateDiagTailX0RatChunk000Sub000Block120Part001

theorem surrogateDiagonalTailChunk000Sub000Block120Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part001] using hcert

def TailChunk000Sub000Block120Part002SupportExplicit : Finset ℕ :=
  ([4985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part002 : ℚ :=
  (620759001875 : ℚ) / 314973620289552384

def SurrogateDiagonalTailChunk000Sub000Block120Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4985
    = surrogateDiagTailX0RatChunk000Sub000Block120Part002

theorem surrogateDiagonalTailChunk000Sub000Block120Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part002] using hcert

def TailChunk000Sub000Block120Part003SupportExplicit : Finset ℕ :=
  ([4987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part003 : ℚ :=
  (388596390625 : ℚ) / 386345594392154802

def SurrogateDiagonalTailChunk000Sub000Block120Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4987
    = surrogateDiagTailX0RatChunk000Sub000Block120Part003

theorem surrogateDiagonalTailChunk000Sub000Block120Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part003] using hcert

def TailChunk000Sub000Block120Part004SupportExplicit : Finset ℕ :=
  ([4989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part004 : ℚ :=
  (34548875 : ℚ) / 10173322554048

def SurrogateDiagonalTailChunk000Sub000Block120Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4989
    = surrogateDiagTailX0RatChunk000Sub000Block120Part004

theorem surrogateDiagonalTailChunk000Sub000Block120Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part004] using hcert

def TailChunk000Sub000Block120Part005SupportExplicit : Finset ℕ :=
  ([4990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part005 : ℚ :=
  (155345687875 : ℚ) / 9842925634048512

def SurrogateDiagonalTailChunk000Sub000Block120Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4990
    = surrogateDiagTailX0RatChunk000Sub000Block120Part005

theorem surrogateDiagonalTailChunk000Sub000Block120Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part005] using hcert

def TailChunk000Sub000Block120Part006SupportExplicit : Finset ℕ :=
  ([4991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part006 : ℚ :=
  (2745605261 : ℚ) / 1366454228198400

def SurrogateDiagonalTailChunk000Sub000Block120Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4991
    = surrogateDiagTailX0RatChunk000Sub000Block120Part006

theorem surrogateDiagonalTailChunk000Sub000Block120Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part006] using hcert

def TailChunk000Sub000Block120Part007SupportExplicit : Finset ℕ :=
  ([4993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part007 : ℚ :=
  (389532015625 : ℚ) / 388208619801280512

def SurrogateDiagonalTailChunk000Sub000Block120Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4993
    = surrogateDiagTailX0RatChunk000Sub000Block120Part007

theorem surrogateDiagonalTailChunk000Sub000Block120Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part007] using hcert

def TailChunk000Sub000Block120Part008SupportExplicit : Finset ℕ :=
  ([4994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part008 : ℚ :=
  (5644401653 : ℚ) / 521855905511040

def SurrogateDiagonalTailChunk000Sub000Block120Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4994
    = surrogateDiagTailX0RatChunk000Sub000Block120Part008

theorem surrogateDiagonalTailChunk000Sub000Block120Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part008] using hcert

def TailChunk000Sub000Block120Part009SupportExplicit : Finset ℕ :=
  ([4997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part009 : ℚ :=
  (184145071625 : ℚ) / 154608033958186896

def SurrogateDiagonalTailChunk000Sub000Block120Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4997
    = surrogateDiagTailX0RatChunk000Sub000Block120Part009

theorem surrogateDiagonalTailChunk000Sub000Block120Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part009] using hcert

def TailChunk000Sub000Block120Part010SupportExplicit : Finset ℕ :=
  ([4999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part010 : ℚ :=
  (390468765625 : ℚ) / 390078374974990002

def SurrogateDiagonalTailChunk000Sub000Block120Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4999
    = surrogateDiagTailX0RatChunk000Sub000Block120Part010

theorem surrogateDiagonalTailChunk000Sub000Block120Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part010] using hcert

def TailChunk000Sub000Block120Part011SupportExplicit : Finset ℕ :=
  ([5001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part011 : ℚ :=
  (125025 : ℚ) / 36992610368

def SurrogateDiagonalTailChunk000Sub000Block120Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5001
    = surrogateDiagTailX0RatChunk000Sub000Block120Part011

theorem surrogateDiagonalTailChunk000Sub000Block120Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part011] using hcert

def TailChunk000Sub000Block120Part012SupportExplicit : Finset ℕ :=
  ([5002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part012 : ℚ :=
  (30017999899 : ℚ) / 3318423552000000

def SurrogateDiagonalTailChunk000Sub000Block120Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5002
    = surrogateDiagTailX0RatChunk000Sub000Block120Part012

theorem surrogateDiagonalTailChunk000Sub000Block120Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part012] using hcert

def TailChunk000Sub000Block120Part013SupportExplicit : Finset ℕ :=
  ([5003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part013 : ℚ :=
  (391093890625 : ℚ) / 391328625175030002

def SurrogateDiagonalTailChunk000Sub000Block120Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5003
    = surrogateDiagTailX0RatChunk000Sub000Block120Part013

theorem surrogateDiagonalTailChunk000Sub000Block120Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part013] using hcert

def TailChunk000Sub000Block120Part014SupportExplicit : Finset ℕ :=
  ([5005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part014 : ℚ :=
  (333732497 : ℚ) / 63713732198400

def SurrogateDiagonalTailChunk000Sub000Block120Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5005
    = surrogateDiagTailX0RatChunk000Sub000Block120Part014

theorem surrogateDiagonalTailChunk000Sub000Block120Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part014] using hcert

def TailChunk000Sub000Block120Part015SupportExplicit : Finset ℕ :=
  ([5006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part015 : ℚ :=
  (782969499775 : ℚ) / 97988719025080008

def SurrogateDiagonalTailChunk000Sub000Block120Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5006
    = surrogateDiagTailX0RatChunk000Sub000Block120Part015

theorem surrogateDiagonalTailChunk000Sub000Block120Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part015] using hcert

def TailChunk000Sub000Block120Part016SupportExplicit : Finset ℕ :=
  ([5007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part016 : ℚ :=
  (34798625 : ℚ) / 10321027181568

def SurrogateDiagonalTailChunk000Sub000Block120Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5007
    = surrogateDiagTailX0RatChunk000Sub000Block120Part016

theorem surrogateDiagonalTailChunk000Sub000Block120Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part016] using hcert

def TailChunk000Sub000Block120Part017SupportExplicit : Finset ℕ :=
  ([5009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part017 : ℚ :=
  (392032515625 : ℚ) / 393209632603840512

def SurrogateDiagonalTailChunk000Sub000Block120Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5009
    = surrogateDiagTailX0RatChunk000Sub000Block120Part017

theorem surrogateDiagonalTailChunk000Sub000Block120Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part017] using hcert

def TailChunk000Sub000Block120Part018SupportExplicit : Finset ℕ :=
  ([5010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part018 : ℚ :=
  (409016683075 : ℚ) / 7777126426902528

def SurrogateDiagonalTailChunk000Sub000Block120Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5010
    = surrogateDiagTailX0RatChunk000Sub000Block120Part018

theorem surrogateDiagonalTailChunk000Sub000Block120Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part018] using hcert

def TailChunk000Sub000Block120Part019SupportExplicit : Finset ℕ :=
  ([5011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part019 : ℚ :=
  (627753025 : ℚ) / 630141023014002

def SurrogateDiagonalTailChunk000Sub000Block120Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5011
    = surrogateDiagTailX0RatChunk000Sub000Block120Part019

theorem surrogateDiagonalTailChunk000Sub000Block120Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part019] using hcert

def TailChunk000Sub000Block120Part020SupportExplicit : Finset ℕ :=
  ([5014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part020 : ℚ :=
  (372348454175 : ℚ) / 39845805294265344

def SurrogateDiagonalTailChunk000Sub000Block120Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5014
    = surrogateDiagTailX0RatChunk000Sub000Block120Part020

theorem surrogateDiagonalTailChunk000Sub000Block120Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part020] using hcert

def TailChunk000Sub000Block120Part021SupportExplicit : Finset ℕ :=
  ([5015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part021 : ℚ :=
  (581847001325 : ℚ) / 237371587018358784

def SurrogateDiagonalTailChunk000Sub000Block120Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5015
    = surrogateDiagTailX0RatChunk000Sub000Block120Part021

theorem surrogateDiagonalTailChunk000Sub000Block120Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part021] using hcert

def TailChunk000Sub000Block120Part022SupportExplicit : Finset ℕ :=
  ([5017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part022 : ℚ :=
  (188796134225 : ℚ) / 168144545981239296

def SurrogateDiagonalTailChunk000Sub000Block120Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5017
    = surrogateDiagTailX0RatChunk000Sub000Block120Part022

theorem surrogateDiagonalTailChunk000Sub000Block120Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part022] using hcert

def TailChunk000Sub000Block120Part023SupportExplicit : Finset ℕ :=
  ([5018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part023 : ℚ :=
  (90340814525 : ℚ) / 8807786339106816

def SurrogateDiagonalTailChunk000Sub000Block120Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5018
    = surrogateDiagTailX0RatChunk000Sub000Block120Part023

theorem surrogateDiagonalTailChunk000Sub000Block120Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part023] using hcert

def TailChunk000Sub000Block120Part024SupportExplicit : Finset ℕ :=
  ([5019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block120Part024 : ℚ :=
  (892513690675 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub000Block120Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5019
    = surrogateDiagTailX0RatChunk000Sub000Block120Part024

theorem surrogateDiagonalTailChunk000Sub000Block120Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block120Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block120Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block120Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block120Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block120Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block120Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block120HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block120Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block120Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block120Part000
    + surrogateDiagTailX0RatChunk000Sub000Block120Part001
    + surrogateDiagTailX0RatChunk000Sub000Block120Part002
    + surrogateDiagTailX0RatChunk000Sub000Block120Part003
    + surrogateDiagTailX0RatChunk000Sub000Block120Part004
    + surrogateDiagTailX0RatChunk000Sub000Block120Part005
    + surrogateDiagTailX0RatChunk000Sub000Block120Part006
    + surrogateDiagTailX0RatChunk000Sub000Block120Part007
    + surrogateDiagTailX0RatChunk000Sub000Block120Part008
    + surrogateDiagTailX0RatChunk000Sub000Block120Part009

def surrogateDiagonalTailChunk000Sub000Block120MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block120Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block120Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block120Part010
    + surrogateDiagTailX0RatChunk000Sub000Block120Part011
    + surrogateDiagTailX0RatChunk000Sub000Block120Part012
    + surrogateDiagTailX0RatChunk000Sub000Block120Part013
    + surrogateDiagTailX0RatChunk000Sub000Block120Part014
    + surrogateDiagTailX0RatChunk000Sub000Block120Part015
    + surrogateDiagTailX0RatChunk000Sub000Block120Part016
    + surrogateDiagTailX0RatChunk000Sub000Block120Part017
    + surrogateDiagTailX0RatChunk000Sub000Block120Part018
    + surrogateDiagTailX0RatChunk000Sub000Block120Part019

def surrogateDiagonalTailChunk000Sub000Block120TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block120Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block120Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block120Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block120Part020
    + surrogateDiagTailX0RatChunk000Sub000Block120Part021
    + surrogateDiagTailX0RatChunk000Sub000Block120Part022
    + surrogateDiagTailX0RatChunk000Sub000Block120Part023
    + surrogateDiagTailX0RatChunk000Sub000Block120Part024

def surrogateDiagonalTailChunk000Sub000Block120Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block120HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block120MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block120TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block120 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block120Part000
    + surrogateDiagTailX0RatChunk000Sub000Block120Part001
    + surrogateDiagTailX0RatChunk000Sub000Block120Part002
    + surrogateDiagTailX0RatChunk000Sub000Block120Part003
    + surrogateDiagTailX0RatChunk000Sub000Block120Part004
    + surrogateDiagTailX0RatChunk000Sub000Block120Part005
    + surrogateDiagTailX0RatChunk000Sub000Block120Part006
    + surrogateDiagTailX0RatChunk000Sub000Block120Part007
    + surrogateDiagTailX0RatChunk000Sub000Block120Part008
    + surrogateDiagTailX0RatChunk000Sub000Block120Part009
    + surrogateDiagTailX0RatChunk000Sub000Block120Part010
    + surrogateDiagTailX0RatChunk000Sub000Block120Part011
    + surrogateDiagTailX0RatChunk000Sub000Block120Part012
    + surrogateDiagTailX0RatChunk000Sub000Block120Part013
    + surrogateDiagTailX0RatChunk000Sub000Block120Part014
    + surrogateDiagTailX0RatChunk000Sub000Block120Part015
    + surrogateDiagTailX0RatChunk000Sub000Block120Part016
    + surrogateDiagTailX0RatChunk000Sub000Block120Part017
    + surrogateDiagTailX0RatChunk000Sub000Block120Part018
    + surrogateDiagTailX0RatChunk000Sub000Block120Part019
    + surrogateDiagTailX0RatChunk000Sub000Block120Part020
    + surrogateDiagTailX0RatChunk000Sub000Block120Part021
    + surrogateDiagTailX0RatChunk000Sub000Block120Part022
    + surrogateDiagTailX0RatChunk000Sub000Block120Part023
    + surrogateDiagTailX0RatChunk000Sub000Block120Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block120_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block120Head + surrogateDiagTailX0RatChunk000Sub000Block120Mid + surrogateDiagTailX0RatChunk000Sub000Block120Tail =
      surrogateDiagTailX0RatChunk000Sub000Block120 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block120Head surrogateDiagTailX0RatChunk000Sub000Block120Mid surrogateDiagTailX0RatChunk000Sub000Block120Tail surrogateDiagTailX0RatChunk000Sub000Block120
  ring

def SurrogateDiagonalTailChunk000Sub000Block120HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block120HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block120Head

def SurrogateDiagonalTailChunk000Sub000Block120MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block120MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block120Mid

def SurrogateDiagonalTailChunk000Sub000Block120TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block120TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block120Tail

theorem surrogateDiagonalTailChunk000Sub000Block120_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block120HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block120MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block120TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block120Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block120 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block120HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block120MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block120TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block120Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block120_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
