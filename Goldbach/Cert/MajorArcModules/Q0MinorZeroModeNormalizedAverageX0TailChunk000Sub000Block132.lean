import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [132,133). -/

/- Block 132 covers tail-support indices [3300,3325) and q from 5482 to 5519. -/

def TailChunk000Sub000Block132Part000SupportExplicit : Finset ℕ :=
  ([5482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part000 : ℚ :=
  (37557891919 : ℚ) / 5637533057155200

def SurrogateDiagonalTailChunk000Sub000Block132Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5482
    = surrogateDiagTailX0RatChunk000Sub000Block132Part000

theorem surrogateDiagonalTailChunk000Sub000Block132Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part000] using hcert

def TailChunk000Sub000Block132Part001SupportExplicit : Finset ℕ :=
  ([5483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part001 : ℚ :=
  (469738890625 : ℚ) / 564576753897835122

def SurrogateDiagonalTailChunk000Sub000Block132Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5483
    = surrogateDiagTailX0RatChunk000Sub000Block132Part001

theorem surrogateDiagonalTailChunk000Sub000Block132Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part001] using hcert

def TailChunk000Sub000Block132Part002SupportExplicit : Finset ℕ :=
  ([5485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part002 : ℚ :=
  (751535151875 : ℚ) / 461826708042153984

def SurrogateDiagonalTailChunk000Sub000Block132Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5485
    = surrogateDiagTailX0RatChunk000Sub000Block132Part002

theorem surrogateDiagonalTailChunk000Sub000Block132Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part002] using hcert

def TailChunk000Sub000Block132Part003SupportExplicit : Finset ℕ :=
  ([5486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part003 : ℚ :=
  (34333643011 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block132Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5486
    = surrogateDiagTailX0RatChunk000Sub000Block132Part003

theorem surrogateDiagonalTailChunk000Sub000Block132Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part003] using hcert

def TailChunk000Sub000Block132Part004SupportExplicit : Finset ℕ :=
  ([5487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part004 : ℚ :=
  (819941221 : ℚ) / 252915725030400

def SurrogateDiagonalTailChunk000Sub000Block132Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5487
    = surrogateDiagTailX0RatChunk000Sub000Block132Part004

theorem surrogateDiagonalTailChunk000Sub000Block132Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part004] using hcert

def TailChunk000Sub000Block132Part005SupportExplicit : Finset ℕ :=
  ([5489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part005 : ℚ :=
  (11286558529 : ℚ) / 10253047535467200

def SurrogateDiagonalTailChunk000Sub000Block132Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5489
    = surrogateDiagTailX0RatChunk000Sub000Block132Part005

theorem surrogateDiagonalTailChunk000Sub000Block132Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part005] using hcert

def TailChunk000Sub000Block132Part006SupportExplicit : Finset ℕ :=
  ([5493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part006 : ℚ :=
  (2252909 : ℚ) / 2411690241600

def SurrogateDiagonalTailChunk000Sub000Block132Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5493
    = surrogateDiagTailX0RatChunk000Sub000Block132Part006

theorem surrogateDiagonalTailChunk000Sub000Block132Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part006] using hcert

def TailChunk000Sub000Block132Part007SupportExplicit : Finset ℕ :=
  ([5494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part007 : ℚ :=
  (9363510377 : ℚ) / 2429251961241600

def SurrogateDiagonalTailChunk000Sub000Block132Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5494
    = surrogateDiagTailX0RatChunk000Sub000Block132Part007

theorem surrogateDiagonalTailChunk000Sub000Block132Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part007] using hcert

def TailChunk000Sub000Block132Part008SupportExplicit : Finset ℕ :=
  ([5495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part008 : ℚ :=
  (35577306875 : ℚ) / 13647959289888768

def SurrogateDiagonalTailChunk000Sub000Block132Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5495
    = surrogateDiagTailX0RatChunk000Sub000Block132Part008

theorem surrogateDiagonalTailChunk000Sub000Block132Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part008] using hcert

def TailChunk000Sub000Block132Part009SupportExplicit : Finset ℕ :=
  ([5497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part009 : ℚ :=
  (223491058925 : ℚ) / 234928347263077776

def SurrogateDiagonalTailChunk000Sub000Block132Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5497
    = surrogateDiagTailX0RatChunk000Sub000Block132Part009

theorem surrogateDiagonalTailChunk000Sub000Block132Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part009] using hcert

def TailChunk000Sub000Block132Part010SupportExplicit : Finset ℕ :=
  ([5498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part010 : ℚ :=
  (944436199975 : ℚ) / 142591544261371008

def SurrogateDiagonalTailChunk000Sub000Block132Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5498
    = surrogateDiagTailX0RatChunk000Sub000Block132Part010

theorem surrogateDiagonalTailChunk000Sub000Block132Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part010] using hcert

def TailChunk000Sub000Block132Part011SupportExplicit : Finset ℕ :=
  ([5501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part011 : ℚ :=
  (30261001 : ℚ) / 36609820500000

def SurrogateDiagonalTailChunk000Sub000Block132Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5501
    = surrogateDiagTailX0RatChunk000Sub000Block132Part011

theorem surrogateDiagonalTailChunk000Sub000Block132Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part011] using hcert

def TailChunk000Sub000Block132Part012SupportExplicit : Finset ℕ :=
  ([5502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part012 : ℚ :=
  (167049323 : ℚ) / 5062900377600

def SurrogateDiagonalTailChunk000Sub000Block132Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5502
    = surrogateDiagTailX0RatChunk000Sub000Block132Part012

theorem surrogateDiagonalTailChunk000Sub000Block132Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part012] using hcert

def TailChunk000Sub000Block132Part013SupportExplicit : Finset ℕ :=
  ([5503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part013 : ℚ :=
  (473172015625 : ℚ) / 572860940638282002

def SurrogateDiagonalTailChunk000Sub000Block132Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5503
    = surrogateDiagTailX0RatChunk000Sub000Block132Part013

theorem surrogateDiagonalTailChunk000Sub000Block132Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part013] using hcert

def TailChunk000Sub000Block132Part014SupportExplicit : Finset ℕ :=
  ([5505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part014 : ℚ :=
  (324620563525 : ℚ) / 61261819828862976

def SurrogateDiagonalTailChunk000Sub000Block132Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5505
    = surrogateDiagTailX0RatChunk000Sub000Block132Part014

theorem surrogateDiagonalTailChunk000Sub000Block132Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part014] using hcert

def TailChunk000Sub000Block132Part015SupportExplicit : Finset ℕ :=
  ([5506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part015 : ℚ :=
  (947186649775 : ℚ) / 143423586076459008

def SurrogateDiagonalTailChunk000Sub000Block132Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5506
    = surrogateDiagTailX0RatChunk000Sub000Block132Part015

theorem surrogateDiagonalTailChunk000Sub000Block132Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part015] using hcert

def TailChunk000Sub000Block132Part016SupportExplicit : Finset ℕ :=
  ([5507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part016 : ℚ :=
  (473860140625 : ℚ) / 574528656975654162

def SurrogateDiagonalTailChunk000Sub000Block132Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5507
    = surrogateDiagTailX0RatChunk000Sub000Block132Part016

theorem surrogateDiagonalTailChunk000Sub000Block132Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part016] using hcert

def TailChunk000Sub000Block132Part017SupportExplicit : Finset ℕ :=
  ([5509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part017 : ℚ :=
  (1585283318575 : ℚ) / 1236864271665495168

def SurrogateDiagonalTailChunk000Sub000Block132Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5509
    = surrogateDiagTailX0RatChunk000Sub000Block132Part017

theorem surrogateDiagonalTailChunk000Sub000Block132Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part017] using hcert

def TailChunk000Sub000Block132Part018SupportExplicit : Finset ℕ :=
  ([5510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part018 : ℚ :=
  (672276443275 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub000Block132Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5510
    = surrogateDiagTailX0RatChunk000Sub000Block132Part018

theorem surrogateDiagonalTailChunk000Sub000Block132Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part018] using hcert

def TailChunk000Sub000Block132Part019SupportExplicit : Finset ℕ :=
  ([5511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part019 : ℚ :=
  (6368799783 : ℚ) / 2025293340339200

def SurrogateDiagonalTailChunk000Sub000Block132Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5511
    = surrogateDiagTailX0RatChunk000Sub000Block132Part019

theorem surrogateDiagonalTailChunk000Sub000Block132Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part019] using hcert

def TailChunk000Sub000Block132Part020SupportExplicit : Finset ℕ :=
  ([5513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part020 : ℚ :=
  (2119121075 : ℚ) / 2332222500989952

def SurrogateDiagonalTailChunk000Sub000Block132Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5513
    = surrogateDiagTailX0RatChunk000Sub000Block132Part020

theorem surrogateDiagonalTailChunk000Sub000Block132Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part020] using hcert

def TailChunk000Sub000Block132Part021SupportExplicit : Finset ℕ :=
  ([5514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part021 : ℚ :=
  (580102629925 : ℚ) / 28413031076961408

def SurrogateDiagonalTailChunk000Sub000Block132Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5514
    = surrogateDiagTailX0RatChunk000Sub000Block132Part021

theorem surrogateDiagonalTailChunk000Sub000Block132Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part021] using hcert

def TailChunk000Sub000Block132Part022SupportExplicit : Finset ℕ :=
  ([5515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part022 : ℚ :=
  (360907033975 : ℚ) / 236011524900966912

def SurrogateDiagonalTailChunk000Sub000Block132Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5515
    = surrogateDiagTailX0RatChunk000Sub000Block132Part022

theorem surrogateDiagonalTailChunk000Sub000Block132Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part022] using hcert

def TailChunk000Sub000Block132Part023SupportExplicit : Finset ℕ :=
  ([5518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part023 : ℚ :=
  (3628966549 : ℚ) / 485850392248320

def SurrogateDiagonalTailChunk000Sub000Block132Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5518
    = surrogateDiagTailX0RatChunk000Sub000Block132Part023

theorem surrogateDiagonalTailChunk000Sub000Block132Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part023] using hcert

def TailChunk000Sub000Block132Part024SupportExplicit : Finset ℕ :=
  ([5519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block132Part024 : ℚ :=
  (475927515625 : ℚ) / 579553659059911122

def SurrogateDiagonalTailChunk000Sub000Block132Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5519
    = surrogateDiagTailX0RatChunk000Sub000Block132Part024

theorem surrogateDiagonalTailChunk000Sub000Block132Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block132Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block132Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block132Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block132Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block132Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block132Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block132HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block132Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block132Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block132Part000
    + surrogateDiagTailX0RatChunk000Sub000Block132Part001
    + surrogateDiagTailX0RatChunk000Sub000Block132Part002
    + surrogateDiagTailX0RatChunk000Sub000Block132Part003
    + surrogateDiagTailX0RatChunk000Sub000Block132Part004
    + surrogateDiagTailX0RatChunk000Sub000Block132Part005
    + surrogateDiagTailX0RatChunk000Sub000Block132Part006
    + surrogateDiagTailX0RatChunk000Sub000Block132Part007
    + surrogateDiagTailX0RatChunk000Sub000Block132Part008
    + surrogateDiagTailX0RatChunk000Sub000Block132Part009

def surrogateDiagonalTailChunk000Sub000Block132MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block132Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block132Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block132Part010
    + surrogateDiagTailX0RatChunk000Sub000Block132Part011
    + surrogateDiagTailX0RatChunk000Sub000Block132Part012
    + surrogateDiagTailX0RatChunk000Sub000Block132Part013
    + surrogateDiagTailX0RatChunk000Sub000Block132Part014
    + surrogateDiagTailX0RatChunk000Sub000Block132Part015
    + surrogateDiagTailX0RatChunk000Sub000Block132Part016
    + surrogateDiagTailX0RatChunk000Sub000Block132Part017
    + surrogateDiagTailX0RatChunk000Sub000Block132Part018
    + surrogateDiagTailX0RatChunk000Sub000Block132Part019

def surrogateDiagonalTailChunk000Sub000Block132TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block132Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block132Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block132Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block132Part020
    + surrogateDiagTailX0RatChunk000Sub000Block132Part021
    + surrogateDiagTailX0RatChunk000Sub000Block132Part022
    + surrogateDiagTailX0RatChunk000Sub000Block132Part023
    + surrogateDiagTailX0RatChunk000Sub000Block132Part024

def surrogateDiagonalTailChunk000Sub000Block132Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block132HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block132MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block132TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block132 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block132Part000
    + surrogateDiagTailX0RatChunk000Sub000Block132Part001
    + surrogateDiagTailX0RatChunk000Sub000Block132Part002
    + surrogateDiagTailX0RatChunk000Sub000Block132Part003
    + surrogateDiagTailX0RatChunk000Sub000Block132Part004
    + surrogateDiagTailX0RatChunk000Sub000Block132Part005
    + surrogateDiagTailX0RatChunk000Sub000Block132Part006
    + surrogateDiagTailX0RatChunk000Sub000Block132Part007
    + surrogateDiagTailX0RatChunk000Sub000Block132Part008
    + surrogateDiagTailX0RatChunk000Sub000Block132Part009
    + surrogateDiagTailX0RatChunk000Sub000Block132Part010
    + surrogateDiagTailX0RatChunk000Sub000Block132Part011
    + surrogateDiagTailX0RatChunk000Sub000Block132Part012
    + surrogateDiagTailX0RatChunk000Sub000Block132Part013
    + surrogateDiagTailX0RatChunk000Sub000Block132Part014
    + surrogateDiagTailX0RatChunk000Sub000Block132Part015
    + surrogateDiagTailX0RatChunk000Sub000Block132Part016
    + surrogateDiagTailX0RatChunk000Sub000Block132Part017
    + surrogateDiagTailX0RatChunk000Sub000Block132Part018
    + surrogateDiagTailX0RatChunk000Sub000Block132Part019
    + surrogateDiagTailX0RatChunk000Sub000Block132Part020
    + surrogateDiagTailX0RatChunk000Sub000Block132Part021
    + surrogateDiagTailX0RatChunk000Sub000Block132Part022
    + surrogateDiagTailX0RatChunk000Sub000Block132Part023
    + surrogateDiagTailX0RatChunk000Sub000Block132Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block132_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block132Head + surrogateDiagTailX0RatChunk000Sub000Block132Mid + surrogateDiagTailX0RatChunk000Sub000Block132Tail =
      surrogateDiagTailX0RatChunk000Sub000Block132 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block132Head surrogateDiagTailX0RatChunk000Sub000Block132Mid surrogateDiagTailX0RatChunk000Sub000Block132Tail surrogateDiagTailX0RatChunk000Sub000Block132
  ring

def SurrogateDiagonalTailChunk000Sub000Block132HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block132HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block132Head

def SurrogateDiagonalTailChunk000Sub000Block132MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block132MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block132Mid

def SurrogateDiagonalTailChunk000Sub000Block132TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block132TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block132Tail

theorem surrogateDiagonalTailChunk000Sub000Block132_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block132HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block132MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block132TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block132Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block132 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block132HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block132MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block132TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block132Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block132_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
