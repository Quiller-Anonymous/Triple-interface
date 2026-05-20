import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [40,50). -/

/-- Block 040 covers tail-support indices [6000,6025) and q from 9913 to 9955. -/

def TailChunk000Sub001Block040Part000SupportExplicit : Finset ℕ :=
  ([9913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part000 : ℚ :=
  (178304439 : ℚ) / 26701160732847040

def SurrogateDiagonalTailChunk000Sub001Block040Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9913
    = surrogateDiagTailX0RatChunk000Sub001Block040Part000

theorem surrogateDiagonalTailChunk000Sub001Block040Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part000] using hcert

def TailChunk000Sub001Block040Part001SupportExplicit : Finset ℕ :=
  ([9914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part001 : ℚ :=
  (383935140625 : ℚ) / 377130848630068512

def SurrogateDiagonalTailChunk000Sub001Block040Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9914
    = surrogateDiagTailX0RatChunk000Sub001Block040Part001

theorem surrogateDiagonalTailChunk000Sub001Block040Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part001] using hcert

def TailChunk000Sub001Block040Part002SupportExplicit : Finset ℕ :=
  ([9915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part002 : ℚ :=
  (10198194803 : ℚ) / 25912020919910400

def SurrogateDiagonalTailChunk000Sub001Block040Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9915
    = surrogateDiagTailX0RatChunk000Sub001Block040Part002

theorem surrogateDiagonalTailChunk000Sub001Block040Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part002] using hcert

def TailChunk000Sub001Block040Part003SupportExplicit : Finset ℕ :=
  ([9917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part003 : ℚ :=
  (3206835271 : ℚ) / 870954276360067200

def SurrogateDiagonalTailChunk000Sub001Block040Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9917
    = surrogateDiagTailX0RatChunk000Sub001Block040Part003

theorem surrogateDiagonalTailChunk000Sub001Block040Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part003] using hcert

def TailChunk000Sub001Block040Part004SupportExplicit : Finset ℕ :=
  ([9919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part004 : ℚ :=
  (1287783875 : ℚ) / 18811160862916608

def SurrogateDiagonalTailChunk000Sub001Block040Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9919
    = surrogateDiagTailX0RatChunk000Sub001Block040Part004

theorem surrogateDiagonalTailChunk000Sub001Block040Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part004] using hcert

def TailChunk000Sub001Block040Part005SupportExplicit : Finset ℕ :=
  ([9921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part005 : ℚ :=
  (341863677425 : ℚ) / 2389616689622289984

def SurrogateDiagonalTailChunk000Sub001Block040Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9921
    = surrogateDiagTailX0RatChunk000Sub001Block040Part005

theorem surrogateDiagonalTailChunk000Sub001Block040Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part005] using hcert

def TailChunk000Sub001Block040Part006SupportExplicit : Finset ℕ :=
  ([9923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block040Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9923
    = surrogateDiagTailX0RatChunk000Sub001Block040Part006

theorem surrogateDiagonalTailChunk000Sub001Block040Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part006] using hcert

def TailChunk000Sub001Block040Part007SupportExplicit : Finset ℕ :=
  ([9926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part007 : ℚ :=
  (24406543525 : ℚ) / 15078951048932352

def SurrogateDiagonalTailChunk000Sub001Block040Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9926
    = surrogateDiagTailX0RatChunk000Sub001Block040Part007

theorem surrogateDiagonalTailChunk000Sub001Block040Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part007] using hcert

def TailChunk000Sub001Block040Part008SupportExplicit : Finset ℕ :=
  ([9929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block040Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9929
    = surrogateDiagTailX0RatChunk000Sub001Block040Part008

theorem surrogateDiagonalTailChunk000Sub001Block040Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part008] using hcert

def TailChunk000Sub001Block040Part009SupportExplicit : Finset ℕ :=
  ([9930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part009 : ℚ :=
  (32776258891 : ℚ) / 4858503922483200

def SurrogateDiagonalTailChunk000Sub001Block040Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9930
    = surrogateDiagTailX0RatChunk000Sub001Block040Part009

theorem surrogateDiagonalTailChunk000Sub001Block040Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part009] using hcert

def TailChunk000Sub001Block040Part010SupportExplicit : Finset ℕ :=
  ([9931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block040Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9931
    = surrogateDiagTailX0RatChunk000Sub001Block040Part010

theorem surrogateDiagonalTailChunk000Sub001Block040Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part010] using hcert

def TailChunk000Sub001Block040Part011SupportExplicit : Finset ℕ :=
  ([9933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part011 : ℚ :=
  (1567455689 : ℚ) / 3226851654082560

def SurrogateDiagonalTailChunk000Sub001Block040Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9933
    = surrogateDiagTailX0RatChunk000Sub001Block040Part011

theorem surrogateDiagonalTailChunk000Sub001Block040Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part011] using hcert

def TailChunk000Sub001Block040Part012SupportExplicit : Finset ℕ :=
  ([9934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part012 : ℚ :=
  (385485765625 : ℚ) / 380183906112117042

def SurrogateDiagonalTailChunk000Sub001Block040Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9934
    = surrogateDiagTailX0RatChunk000Sub001Block040Part012

theorem surrogateDiagonalTailChunk000Sub001Block040Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part012] using hcert

def TailChunk000Sub001Block040Part013SupportExplicit : Finset ℕ :=
  ([9935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part013 : ℚ :=
  (185122738675 : ℚ) / 2489566947653325312

def SurrogateDiagonalTailChunk000Sub001Block040Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9935
    = surrogateDiagTailX0RatChunk000Sub001Block040Part013

theorem surrogateDiagonalTailChunk000Sub001Block040Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part013] using hcert

def TailChunk000Sub001Block040Part014SupportExplicit : Finset ℕ :=
  ([9937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part014 : ℚ :=
  (9915553975 : ℚ) / 1218088684047044808

def SurrogateDiagonalTailChunk000Sub001Block040Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9937
    = surrogateDiagTailX0RatChunk000Sub001Block040Part014

theorem surrogateDiagonalTailChunk000Sub001Block040Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part014] using hcert

def TailChunk000Sub001Block040Part015SupportExplicit : Finset ℕ :=
  ([9938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part015 : ℚ :=
  (385796265625 : ℚ) / 380796735173571072

def SurrogateDiagonalTailChunk000Sub001Block040Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9938
    = surrogateDiagTailX0RatChunk000Sub001Block040Part015

theorem surrogateDiagonalTailChunk000Sub001Block040Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part015] using hcert

def TailChunk000Sub001Block040Part016SupportExplicit : Finset ℕ :=
  ([9939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part016 : ℚ :=
  (685759280075 : ℚ) / 2407011461837881344

def SurrogateDiagonalTailChunk000Sub001Block040Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9939
    = surrogateDiagTailX0RatChunk000Sub001Block040Part016

theorem surrogateDiagonalTailChunk000Sub001Block040Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part016] using hcert

def TailChunk000Sub001Block040Part017SupportExplicit : Finset ℕ :=
  ([9941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block040Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9941
    = surrogateDiagTailX0RatChunk000Sub001Block040Part017

theorem surrogateDiagonalTailChunk000Sub001Block040Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part017] using hcert

def TailChunk000Sub001Block040Part018SupportExplicit : Finset ℕ :=
  ([9942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part018 : ℚ :=
  (34300025 : ℚ) / 10027208982528

def SurrogateDiagonalTailChunk000Sub001Block040Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9942
    = surrogateDiagTailX0RatChunk000Sub001Block040Part018

theorem surrogateDiagonalTailChunk000Sub001Block040Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part018] using hcert

def TailChunk000Sub001Block040Part019SupportExplicit : Finset ℕ :=
  ([9943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part019 : ℚ :=
  (346489421 : ℚ) / 111599416252166400

def SurrogateDiagonalTailChunk000Sub001Block040Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9943
    = surrogateDiagTailX0RatChunk000Sub001Block040Part019

theorem surrogateDiagonalTailChunk000Sub001Block040Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part019] using hcert

def TailChunk000Sub001Block040Part020SupportExplicit : Finset ℕ :=
  ([9946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part020 : ℚ :=
  (386417640625 : ℚ) / 382024615629356832

def SurrogateDiagonalTailChunk000Sub001Block040Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9946
    = surrogateDiagTailX0RatChunk000Sub001Block040Part020

theorem surrogateDiagonalTailChunk000Sub001Block040Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part020] using hcert

def TailChunk000Sub001Block040Part021SupportExplicit : Finset ℕ :=
  ([9949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block040Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9949
    = surrogateDiagTailX0RatChunk000Sub001Block040Part021

theorem surrogateDiagonalTailChunk000Sub001Block040Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part021] using hcert

def TailChunk000Sub001Block040Part022SupportExplicit : Finset ℕ :=
  ([9951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part022 : ℚ :=
  (2156337565 : ℚ) / 6545989496752128

def SurrogateDiagonalTailChunk000Sub001Block040Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9951
    = surrogateDiagTailX0RatChunk000Sub001Block040Part022

theorem surrogateDiagonalTailChunk000Sub001Block040Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part022] using hcert

def TailChunk000Sub001Block040Part023SupportExplicit : Finset ℕ :=
  ([9953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part023 : ℚ :=
  (1436156425 : ℚ) / 323371123377537024

def SurrogateDiagonalTailChunk000Sub001Block040Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9953
    = surrogateDiagTailX0RatChunk000Sub001Block040Part023

theorem surrogateDiagonalTailChunk000Sub001Block040Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part023] using hcert

def TailChunk000Sub001Block040Part024SupportExplicit : Finset ℕ :=
  ([9955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block040Part024 : ℚ :=
  (1304575067 : ℚ) / 13439615385600000

def SurrogateDiagonalTailChunk000Sub001Block040Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9955
    = surrogateDiagTailX0RatChunk000Sub001Block040Part024

theorem surrogateDiagonalTailChunk000Sub001Block040Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block040Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block040Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block040Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block040Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block040Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block040Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block040HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block040Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block040Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block040Part000
    + surrogateDiagTailX0RatChunk000Sub001Block040Part001
    + surrogateDiagTailX0RatChunk000Sub001Block040Part002
    + surrogateDiagTailX0RatChunk000Sub001Block040Part003
    + surrogateDiagTailX0RatChunk000Sub001Block040Part004
    + surrogateDiagTailX0RatChunk000Sub001Block040Part005
    + surrogateDiagTailX0RatChunk000Sub001Block040Part006
    + surrogateDiagTailX0RatChunk000Sub001Block040Part007
    + surrogateDiagTailX0RatChunk000Sub001Block040Part008
    + surrogateDiagTailX0RatChunk000Sub001Block040Part009

def surrogateDiagonalTailChunk000Sub001Block040MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block040Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block040Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block040Part010
    + surrogateDiagTailX0RatChunk000Sub001Block040Part011
    + surrogateDiagTailX0RatChunk000Sub001Block040Part012
    + surrogateDiagTailX0RatChunk000Sub001Block040Part013
    + surrogateDiagTailX0RatChunk000Sub001Block040Part014
    + surrogateDiagTailX0RatChunk000Sub001Block040Part015
    + surrogateDiagTailX0RatChunk000Sub001Block040Part016
    + surrogateDiagTailX0RatChunk000Sub001Block040Part017
    + surrogateDiagTailX0RatChunk000Sub001Block040Part018
    + surrogateDiagTailX0RatChunk000Sub001Block040Part019

def surrogateDiagonalTailChunk000Sub001Block040TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block040Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block040Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block040Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block040Part020
    + surrogateDiagTailX0RatChunk000Sub001Block040Part021
    + surrogateDiagTailX0RatChunk000Sub001Block040Part022
    + surrogateDiagTailX0RatChunk000Sub001Block040Part023
    + surrogateDiagTailX0RatChunk000Sub001Block040Part024

def surrogateDiagonalTailChunk000Sub001Block040Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block040HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block040MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block040TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block040 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block040Part000
    + surrogateDiagTailX0RatChunk000Sub001Block040Part001
    + surrogateDiagTailX0RatChunk000Sub001Block040Part002
    + surrogateDiagTailX0RatChunk000Sub001Block040Part003
    + surrogateDiagTailX0RatChunk000Sub001Block040Part004
    + surrogateDiagTailX0RatChunk000Sub001Block040Part005
    + surrogateDiagTailX0RatChunk000Sub001Block040Part006
    + surrogateDiagTailX0RatChunk000Sub001Block040Part007
    + surrogateDiagTailX0RatChunk000Sub001Block040Part008
    + surrogateDiagTailX0RatChunk000Sub001Block040Part009
    + surrogateDiagTailX0RatChunk000Sub001Block040Part010
    + surrogateDiagTailX0RatChunk000Sub001Block040Part011
    + surrogateDiagTailX0RatChunk000Sub001Block040Part012
    + surrogateDiagTailX0RatChunk000Sub001Block040Part013
    + surrogateDiagTailX0RatChunk000Sub001Block040Part014
    + surrogateDiagTailX0RatChunk000Sub001Block040Part015
    + surrogateDiagTailX0RatChunk000Sub001Block040Part016
    + surrogateDiagTailX0RatChunk000Sub001Block040Part017
    + surrogateDiagTailX0RatChunk000Sub001Block040Part018
    + surrogateDiagTailX0RatChunk000Sub001Block040Part019
    + surrogateDiagTailX0RatChunk000Sub001Block040Part020
    + surrogateDiagTailX0RatChunk000Sub001Block040Part021
    + surrogateDiagTailX0RatChunk000Sub001Block040Part022
    + surrogateDiagTailX0RatChunk000Sub001Block040Part023
    + surrogateDiagTailX0RatChunk000Sub001Block040Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block040_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block040Head + surrogateDiagTailX0RatChunk000Sub001Block040Mid + surrogateDiagTailX0RatChunk000Sub001Block040Tail =
      surrogateDiagTailX0RatChunk000Sub001Block040 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block040Head surrogateDiagTailX0RatChunk000Sub001Block040Mid surrogateDiagTailX0RatChunk000Sub001Block040Tail surrogateDiagTailX0RatChunk000Sub001Block040
  ring

def SurrogateDiagonalTailChunk000Sub001Block040HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block040HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block040Head

def SurrogateDiagonalTailChunk000Sub001Block040MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block040MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block040Mid

def SurrogateDiagonalTailChunk000Sub001Block040TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block040TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block040Tail

theorem surrogateDiagonalTailChunk000Sub001Block040_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block040HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block040MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block040TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block040Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block040 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block040HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block040MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block040TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block040Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block040_eq_head_add_mid_add_tail

/-- Block 041 covers tail-support indices [6025,6050) and q from 9957 to 9995. -/

def TailChunk000Sub001Block041Part000SupportExplicit : Finset ℕ :=
  ([9957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part000 : ℚ :=
  (688245032525 : ℚ) / 2424501028192509504

def SurrogateDiagonalTailChunk000Sub001Block041Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9957
    = surrogateDiagTailX0RatChunk000Sub001Block041Part000

theorem surrogateDiagonalTailChunk000Sub001Block041Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part000] using hcert

def TailChunk000Sub001Block041Part001SupportExplicit : Finset ℕ :=
  ([9958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part001 : ℚ :=
  (713394025175 : ℚ) / 552046040204534784

def SurrogateDiagonalTailChunk000Sub001Block041Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9958
    = surrogateDiagTailX0RatChunk000Sub001Block041Part001

theorem surrogateDiagonalTailChunk000Sub001Block041Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part001] using hcert

def TailChunk000Sub001Block041Part002SupportExplicit : Finset ℕ :=
  ([9959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part002 : ℚ :=
  (73261841825 : ℚ) / 10200526155331928064

def SurrogateDiagonalTailChunk000Sub001Block041Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9959
    = surrogateDiagTailX0RatChunk000Sub001Block041Part002

theorem surrogateDiagonalTailChunk000Sub001Block041Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part002] using hcert

def TailChunk000Sub001Block041Part003SupportExplicit : Finset ℕ :=
  ([9961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part003 : ℚ :=
  (7053031825 : ℚ) / 245378488067796672

def SurrogateDiagonalTailChunk000Sub001Block041Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9961
    = surrogateDiagTailX0RatChunk000Sub001Block041Part003

theorem surrogateDiagonalTailChunk000Sub001Block041Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part003] using hcert

def TailChunk000Sub001Block041Part004SupportExplicit : Finset ℕ :=
  ([9962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part004 : ℚ :=
  (484920027075 : ℚ) / 397115593301426176

def SurrogateDiagonalTailChunk000Sub001Block041Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9962
    = surrogateDiagTailX0RatChunk000Sub001Block041Part004

theorem surrogateDiagonalTailChunk000Sub001Block041Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part004] using hcert

def TailChunk000Sub001Block041Part005SupportExplicit : Finset ℕ :=
  ([9965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part005 : ℚ :=
  (372482205725 : ℚ) / 5039577924632838144

def SurrogateDiagonalTailChunk000Sub001Block041Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9965
    = surrogateDiagTailX0RatChunk000Sub001Block041Part005

theorem surrogateDiagonalTailChunk000Sub001Block041Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part005] using hcert

def TailChunk000Sub001Block041Part006SupportExplicit : Finset ℕ :=
  ([9966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part006 : ℚ :=
  (7476260441 : ℚ) / 1620324000000000

def SurrogateDiagonalTailChunk000Sub001Block041Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9966
    = surrogateDiagTailX0RatChunk000Sub001Block041Part006

theorem surrogateDiagonalTailChunk000Sub001Block041Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part006] using hcert

def TailChunk000Sub001Block041Part007SupportExplicit : Finset ℕ :=
  ([9967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block041Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9967
    = surrogateDiagTailX0RatChunk000Sub001Block041Part007

theorem surrogateDiagonalTailChunk000Sub001Block041Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part007] using hcert

def TailChunk000Sub001Block041Part008SupportExplicit : Finset ℕ :=
  ([9969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part008 : ℚ :=
  (345177677225 : ℚ) / 2436213572242511424

def SurrogateDiagonalTailChunk000Sub001Block041Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9969
    = surrogateDiagTailX0RatChunk000Sub001Block041Part008

theorem surrogateDiagonalTailChunk000Sub001Block041Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part008] using hcert

def TailChunk000Sub001Block041Part009SupportExplicit : Finset ℕ :=
  ([9970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part009 : ℚ :=
  (620759001875 : ℚ) / 314973620289552384

def SurrogateDiagonalTailChunk000Sub001Block041Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9970
    = surrogateDiagTailX0RatChunk000Sub001Block041Part009

theorem surrogateDiagonalTailChunk000Sub001Block041Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part009] using hcert

def TailChunk000Sub001Block041Part010SupportExplicit : Finset ℕ :=
  ([9973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block041Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9973
    = surrogateDiagTailX0RatChunk000Sub001Block041Part010

theorem surrogateDiagonalTailChunk000Sub001Block041Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part010] using hcert

def TailChunk000Sub001Block041Part011SupportExplicit : Finset ℕ :=
  ([9974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part011 : ℚ :=
  (388596390625 : ℚ) / 386345594392154802

def SurrogateDiagonalTailChunk000Sub001Block041Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9974
    = surrogateDiagTailX0RatChunk000Sub001Block041Part011

theorem surrogateDiagonalTailChunk000Sub001Block041Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part011] using hcert

def TailChunk000Sub001Block041Part012SupportExplicit : Finset ℕ :=
  ([9977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part012 : ℚ :=
  (69182189 : ℚ) / 4492709954958528

def SurrogateDiagonalTailChunk000Sub001Block041Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9977
    = surrogateDiagTailX0RatChunk000Sub001Block041Part012

theorem surrogateDiagonalTailChunk000Sub001Block041Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part012] using hcert

def TailChunk000Sub001Block041Part013SupportExplicit : Finset ℕ :=
  ([9978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part013 : ℚ :=
  (34548875 : ℚ) / 10173322554048

def SurrogateDiagonalTailChunk000Sub001Block041Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9978
    = surrogateDiagTailX0RatChunk000Sub001Block041Part013

theorem surrogateDiagonalTailChunk000Sub001Block041Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part013] using hcert

def TailChunk000Sub001Block041Part014SupportExplicit : Finset ℕ :=
  ([9979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part014 : ℚ :=
  (65949675525 : ℚ) / 6441336666989264896

def SurrogateDiagonalTailChunk000Sub001Block041Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9979
    = surrogateDiagTailX0RatChunk000Sub001Block041Part014

theorem surrogateDiagonalTailChunk000Sub001Block041Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part014] using hcert

def TailChunk000Sub001Block041Part015SupportExplicit : Finset ℕ :=
  ([9982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part015 : ℚ :=
  (2745605261 : ℚ) / 1366454228198400

def SurrogateDiagonalTailChunk000Sub001Block041Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9982
    = surrogateDiagTailX0RatChunk000Sub001Block041Part015

theorem surrogateDiagonalTailChunk000Sub001Block041Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part015] using hcert

def TailChunk000Sub001Block041Part016SupportExplicit : Finset ℕ :=
  ([9983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part016 : ℚ :=
  (33480051425 : ℚ) / 11382023212331295744

def SurrogateDiagonalTailChunk000Sub001Block041Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9983
    = surrogateDiagTailX0RatChunk000Sub001Block041Part016

theorem surrogateDiagonalTailChunk000Sub001Block041Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part016] using hcert

def TailChunk000Sub001Block041Part017SupportExplicit : Finset ℕ :=
  ([9985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part017 : ℚ :=
  (499152925525 : ℚ) / 10160357097570336768

def SurrogateDiagonalTailChunk000Sub001Block041Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9985
    = surrogateDiagTailX0RatChunk000Sub001Block041Part017

theorem surrogateDiagonalTailChunk000Sub001Block041Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part017] using hcert

def TailChunk000Sub001Block041Part018SupportExplicit : Finset ℕ :=
  ([9986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part018 : ℚ :=
  (389532015625 : ℚ) / 388208619801280512

def SurrogateDiagonalTailChunk000Sub001Block041Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9986
    = surrogateDiagTailX0RatChunk000Sub001Block041Part018

theorem surrogateDiagonalTailChunk000Sub001Block041Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part018] using hcert

def TailChunk000Sub001Block041Part019SupportExplicit : Finset ℕ :=
  ([9987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part019 : ℚ :=
  (173212276075 : ℚ) / 1226930946532442112

def SurrogateDiagonalTailChunk000Sub001Block041Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9987
    = surrogateDiagTailX0RatChunk000Sub001Block041Part019

theorem surrogateDiagonalTailChunk000Sub001Block041Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part019] using hcert

def TailChunk000Sub001Block041Part020SupportExplicit : Finset ℕ :=
  ([9989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part020 : ℚ :=
  (21277714675 : ℚ) / 744453296550812736

def SurrogateDiagonalTailChunk000Sub001Block041Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9989
    = surrogateDiagTailX0RatChunk000Sub001Block041Part020

theorem surrogateDiagonalTailChunk000Sub001Block041Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part020] using hcert

def TailChunk000Sub001Block041Part021SupportExplicit : Finset ℕ :=
  ([9991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part021 : ℚ :=
  (30585864725 : ℚ) / 11494298794195943424

def SurrogateDiagonalTailChunk000Sub001Block041Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9991
    = surrogateDiagTailX0RatChunk000Sub001Block041Part021

theorem surrogateDiagonalTailChunk000Sub001Block041Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part021] using hcert

def TailChunk000Sub001Block041Part022SupportExplicit : Finset ℕ :=
  ([9993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part022 : ℚ :=
  (2774725417 : ℚ) / 19678127352102720

def SurrogateDiagonalTailChunk000Sub001Block041Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9993
    = surrogateDiagTailX0RatChunk000Sub001Block041Part022

theorem surrogateDiagonalTailChunk000Sub001Block041Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part022] using hcert

def TailChunk000Sub001Block041Part023SupportExplicit : Finset ℕ :=
  ([9994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part023 : ℚ :=
  (184145071625 : ℚ) / 154608033958186896

def SurrogateDiagonalTailChunk000Sub001Block041Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9994
    = surrogateDiagTailX0RatChunk000Sub001Block041Part023

theorem surrogateDiagonalTailChunk000Sub001Block041Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part023] using hcert

def TailChunk000Sub001Block041Part024SupportExplicit : Finset ℕ :=
  ([9995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block041Part024 : ℚ :=
  (166717075075 : ℚ) / 3400380406443350016

def SurrogateDiagonalTailChunk000Sub001Block041Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9995
    = surrogateDiagTailX0RatChunk000Sub001Block041Part024

theorem surrogateDiagonalTailChunk000Sub001Block041Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block041Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block041Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block041Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block041Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block041Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block041Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block041HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block041Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block041Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block041Part000
    + surrogateDiagTailX0RatChunk000Sub001Block041Part001
    + surrogateDiagTailX0RatChunk000Sub001Block041Part002
    + surrogateDiagTailX0RatChunk000Sub001Block041Part003
    + surrogateDiagTailX0RatChunk000Sub001Block041Part004
    + surrogateDiagTailX0RatChunk000Sub001Block041Part005
    + surrogateDiagTailX0RatChunk000Sub001Block041Part006
    + surrogateDiagTailX0RatChunk000Sub001Block041Part007
    + surrogateDiagTailX0RatChunk000Sub001Block041Part008
    + surrogateDiagTailX0RatChunk000Sub001Block041Part009

def surrogateDiagonalTailChunk000Sub001Block041MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block041Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block041Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block041Part010
    + surrogateDiagTailX0RatChunk000Sub001Block041Part011
    + surrogateDiagTailX0RatChunk000Sub001Block041Part012
    + surrogateDiagTailX0RatChunk000Sub001Block041Part013
    + surrogateDiagTailX0RatChunk000Sub001Block041Part014
    + surrogateDiagTailX0RatChunk000Sub001Block041Part015
    + surrogateDiagTailX0RatChunk000Sub001Block041Part016
    + surrogateDiagTailX0RatChunk000Sub001Block041Part017
    + surrogateDiagTailX0RatChunk000Sub001Block041Part018
    + surrogateDiagTailX0RatChunk000Sub001Block041Part019

def surrogateDiagonalTailChunk000Sub001Block041TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block041Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block041Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block041Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block041Part020
    + surrogateDiagTailX0RatChunk000Sub001Block041Part021
    + surrogateDiagTailX0RatChunk000Sub001Block041Part022
    + surrogateDiagTailX0RatChunk000Sub001Block041Part023
    + surrogateDiagTailX0RatChunk000Sub001Block041Part024

def surrogateDiagonalTailChunk000Sub001Block041Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block041HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block041MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block041TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block041 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block041Part000
    + surrogateDiagTailX0RatChunk000Sub001Block041Part001
    + surrogateDiagTailX0RatChunk000Sub001Block041Part002
    + surrogateDiagTailX0RatChunk000Sub001Block041Part003
    + surrogateDiagTailX0RatChunk000Sub001Block041Part004
    + surrogateDiagTailX0RatChunk000Sub001Block041Part005
    + surrogateDiagTailX0RatChunk000Sub001Block041Part006
    + surrogateDiagTailX0RatChunk000Sub001Block041Part007
    + surrogateDiagTailX0RatChunk000Sub001Block041Part008
    + surrogateDiagTailX0RatChunk000Sub001Block041Part009
    + surrogateDiagTailX0RatChunk000Sub001Block041Part010
    + surrogateDiagTailX0RatChunk000Sub001Block041Part011
    + surrogateDiagTailX0RatChunk000Sub001Block041Part012
    + surrogateDiagTailX0RatChunk000Sub001Block041Part013
    + surrogateDiagTailX0RatChunk000Sub001Block041Part014
    + surrogateDiagTailX0RatChunk000Sub001Block041Part015
    + surrogateDiagTailX0RatChunk000Sub001Block041Part016
    + surrogateDiagTailX0RatChunk000Sub001Block041Part017
    + surrogateDiagTailX0RatChunk000Sub001Block041Part018
    + surrogateDiagTailX0RatChunk000Sub001Block041Part019
    + surrogateDiagTailX0RatChunk000Sub001Block041Part020
    + surrogateDiagTailX0RatChunk000Sub001Block041Part021
    + surrogateDiagTailX0RatChunk000Sub001Block041Part022
    + surrogateDiagTailX0RatChunk000Sub001Block041Part023
    + surrogateDiagTailX0RatChunk000Sub001Block041Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block041_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block041Head + surrogateDiagTailX0RatChunk000Sub001Block041Mid + surrogateDiagTailX0RatChunk000Sub001Block041Tail =
      surrogateDiagTailX0RatChunk000Sub001Block041 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block041Head surrogateDiagTailX0RatChunk000Sub001Block041Mid surrogateDiagTailX0RatChunk000Sub001Block041Tail surrogateDiagTailX0RatChunk000Sub001Block041
  ring

def SurrogateDiagonalTailChunk000Sub001Block041HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block041HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block041Head

def SurrogateDiagonalTailChunk000Sub001Block041MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block041MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block041Mid

def SurrogateDiagonalTailChunk000Sub001Block041TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block041TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block041Tail

theorem surrogateDiagonalTailChunk000Sub001Block041_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block041HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block041MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block041TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block041Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block041 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block041HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block041MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block041TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block041Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block041_eq_head_add_mid_add_tail

/-- Block 042 covers tail-support indices [6050,6075) and q from 9997 to 10034. -/

def TailChunk000Sub001Block042Part000SupportExplicit : Finset ℕ :=
  ([9997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part000 : ℚ :=
  (224715538375 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk000Sub001Block042Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9997
    = surrogateDiagTailX0RatChunk000Sub001Block042Part000

theorem surrogateDiagonalTailChunk000Sub001Block042Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part000] using hcert

def TailChunk000Sub001Block042Part001SupportExplicit : Finset ℕ :=
  ([9998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part001 : ℚ :=
  (390468765625 : ℚ) / 390078374974990002

def SurrogateDiagonalTailChunk000Sub001Block042Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9998
    = surrogateDiagTailX0RatChunk000Sub001Block042Part001

theorem surrogateDiagonalTailChunk000Sub001Block042Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part001] using hcert

def TailChunk000Sub001Block042Part002SupportExplicit : Finset ℕ :=
  ([10001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part002 : ℚ :=
  (1514309173075 : ℚ) / 5747149397097971712

def SurrogateDiagonalTailChunk000Sub001Block042Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10001
    = surrogateDiagTailX0RatChunk000Sub001Block042Part002

theorem surrogateDiagonalTailChunk000Sub001Block042Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part002] using hcert

def TailChunk000Sub001Block042Part003SupportExplicit : Finset ℕ :=
  ([10002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part003 : ℚ :=
  (125025 : ℚ) / 36992610368

def SurrogateDiagonalTailChunk000Sub001Block042Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10002
    = surrogateDiagTailX0RatChunk000Sub001Block042Part003

theorem surrogateDiagonalTailChunk000Sub001Block042Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part003] using hcert

def TailChunk000Sub001Block042Part004SupportExplicit : Finset ℕ :=
  ([10003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part004 : ℚ :=
  (276285968075 : ℚ) / 748638547223970816

def SurrogateDiagonalTailChunk000Sub001Block042Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10003
    = surrogateDiagTailX0RatChunk000Sub001Block042Part004

theorem surrogateDiagonalTailChunk000Sub001Block042Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part004] using hcert

def TailChunk000Sub001Block042Part005SupportExplicit : Finset ℕ :=
  ([10005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part005 : ℚ :=
  (2295415621525 : ℚ) / 1474720289865596928

def SurrogateDiagonalTailChunk000Sub001Block042Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10005
    = surrogateDiagTailX0RatChunk000Sub001Block042Part005

theorem surrogateDiagonalTailChunk000Sub001Block042Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part005] using hcert

def TailChunk000Sub001Block042Part006SupportExplicit : Finset ℕ :=
  ([10006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part006 : ℚ :=
  (391093890625 : ℚ) / 391328625175030002

def SurrogateDiagonalTailChunk000Sub001Block042Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10006
    = surrogateDiagTailX0RatChunk000Sub001Block042Part006

theorem surrogateDiagonalTailChunk000Sub001Block042Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part006] using hcert

def TailChunk000Sub001Block042Part007SupportExplicit : Finset ℕ :=
  ([10007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part007 : ℚ :=
  (1564688265625 : ℚ) / 6266266508101890162

def SurrogateDiagonalTailChunk000Sub001Block042Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10007
    = surrogateDiagTailX0RatChunk000Sub001Block042Part007

theorem surrogateDiagonalTailChunk000Sub001Block042Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part007] using hcert

def TailChunk000Sub001Block042Part008SupportExplicit : Finset ℕ :=
  ([10009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part008 : ℚ :=
  (1565313765625 : ℚ) / 6271278017605120512

def SurrogateDiagonalTailChunk000Sub001Block042Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10009
    = surrogateDiagTailX0RatChunk000Sub001Block042Part008

theorem surrogateDiagonalTailChunk000Sub001Block042Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part008] using hcert

def TailChunk000Sub001Block042Part009SupportExplicit : Finset ℕ :=
  ([10010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part009 : ℚ :=
  (333732497 : ℚ) / 63713732198400

def SurrogateDiagonalTailChunk000Sub001Block042Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10010
    = surrogateDiagTailX0RatChunk000Sub001Block042Part009

theorem surrogateDiagonalTailChunk000Sub001Block042Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part009] using hcert

def TailChunk000Sub001Block042Part010SupportExplicit : Finset ℕ :=
  ([10011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part010 : ℚ :=
  (168853171 : ℚ) / 219439223068800

def SurrogateDiagonalTailChunk000Sub001Block042Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10011
    = surrogateDiagTailX0RatChunk000Sub001Block042Part010

theorem surrogateDiagonalTailChunk000Sub001Block042Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part010] using hcert

def TailChunk000Sub001Block042Part011SupportExplicit : Finset ℕ :=
  ([10013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part011 : ℚ :=
  (100739956349 : ℚ) / 278683864635801600

def SurrogateDiagonalTailChunk000Sub001Block042Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10013
    = surrogateDiagTailX0RatChunk000Sub001Block042Part011

theorem surrogateDiagonalTailChunk000Sub001Block042Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part011] using hcert

def TailChunk000Sub001Block042Part012SupportExplicit : Finset ℕ :=
  ([10014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part012 : ℚ :=
  (34798625 : ℚ) / 10321027181568

def SurrogateDiagonalTailChunk000Sub001Block042Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10014
    = surrogateDiagTailX0RatChunk000Sub001Block042Part012

theorem surrogateDiagonalTailChunk000Sub001Block042Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part012] using hcert

def TailChunk000Sub001Block042Part013SupportExplicit : Finset ℕ :=
  ([10015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part013 : ℚ :=
  (214807439325 : ℚ) / 489670365965068288

def SurrogateDiagonalTailChunk000Sub001Block042Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10015
    = surrogateDiagTailX0RatChunk000Sub001Block042Part013

theorem surrogateDiagonalTailChunk000Sub001Block042Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part013] using hcert

def TailChunk000Sub001Block042Part014SupportExplicit : Finset ℕ :=
  ([10018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part014 : ℚ :=
  (392032515625 : ℚ) / 393209632603840512

def SurrogateDiagonalTailChunk000Sub001Block042Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10018
    = surrogateDiagTailX0RatChunk000Sub001Block042Part014

theorem surrogateDiagonalTailChunk000Sub001Block042Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part014] using hcert

def TailChunk000Sub001Block042Part015SupportExplicit : Finset ℕ :=
  ([10019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part015 : ℚ :=
  (222916329425 : ℚ) / 834857197897089024

def SurrogateDiagonalTailChunk000Sub001Block042Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10019
    = surrogateDiagTailX0RatChunk000Sub001Block042Part015

theorem surrogateDiagonalTailChunk000Sub001Block042Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part015] using hcert

def TailChunk000Sub001Block042Part016SupportExplicit : Finset ℕ :=
  ([10021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part016 : ℚ :=
  (1812785391 : ℚ) / 5715722999350000

def SurrogateDiagonalTailChunk000Sub001Block042Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10021
    = surrogateDiagTailX0RatChunk000Sub001Block042Part016

theorem surrogateDiagonalTailChunk000Sub001Block042Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part016] using hcert

def TailChunk000Sub001Block042Part017SupportExplicit : Finset ℕ :=
  ([10022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part017 : ℚ :=
  (627753025 : ℚ) / 630141023014002

def SurrogateDiagonalTailChunk000Sub001Block042Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10022
    = surrogateDiagTailX0RatChunk000Sub001Block042Part017

theorem surrogateDiagonalTailChunk000Sub001Block042Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part017] using hcert

def TailChunk000Sub001Block042Part018SupportExplicit : Finset ℕ :=
  ([10023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part018 : ℚ :=
  (193006099975 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub001Block042Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10023
    = surrogateDiagTailX0RatChunk000Sub001Block042Part018

theorem surrogateDiagonalTailChunk000Sub001Block042Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part018] using hcert

def TailChunk000Sub001Block042Part019SupportExplicit : Finset ℕ :=
  ([10027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part019 : ℚ :=
  (119887596797 : ℚ) / 446397665008665600

def SurrogateDiagonalTailChunk000Sub001Block042Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10027
    = surrogateDiagTailX0RatChunk000Sub001Block042Part019

theorem surrogateDiagonalTailChunk000Sub001Block042Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part019] using hcert

def TailChunk000Sub001Block042Part020SupportExplicit : Finset ℕ :=
  ([10029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part020 : ℚ :=
  (872871138025 : ℚ) / 1247707059846626592

def SurrogateDiagonalTailChunk000Sub001Block042Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10029
    = surrogateDiagTailX0RatChunk000Sub001Block042Part020

theorem surrogateDiagonalTailChunk000Sub001Block042Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part020] using hcert

def TailChunk000Sub001Block042Part021SupportExplicit : Finset ℕ :=
  ([10030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part021 : ℚ :=
  (581847001325 : ℚ) / 237371587018358784

def SurrogateDiagonalTailChunk000Sub001Block042Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10030
    = surrogateDiagTailX0RatChunk000Sub001Block042Part021

theorem surrogateDiagonalTailChunk000Sub001Block042Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part021] using hcert

def TailChunk000Sub001Block042Part022SupportExplicit : Finset ℕ :=
  ([10031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part022 : ℚ :=
  (277835372975 : ℚ) / 757061964204097536

def SurrogateDiagonalTailChunk000Sub001Block042Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10031
    = surrogateDiagTailX0RatChunk000Sub001Block042Part022

theorem surrogateDiagonalTailChunk000Sub001Block042Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part022] using hcert

def TailChunk000Sub001Block042Part023SupportExplicit : Finset ℕ :=
  ([10033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part023 : ℚ :=
  (3049665151025 : ℚ) / 11664267058550643264

def SurrogateDiagonalTailChunk000Sub001Block042Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10033
    = surrogateDiagTailX0RatChunk000Sub001Block042Part023

theorem surrogateDiagonalTailChunk000Sub001Block042Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part023] using hcert

def TailChunk000Sub001Block042Part024SupportExplicit : Finset ℕ :=
  ([10034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block042Part024 : ℚ :=
  (188796134225 : ℚ) / 168144545981239296

def SurrogateDiagonalTailChunk000Sub001Block042Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10034
    = surrogateDiagTailX0RatChunk000Sub001Block042Part024

theorem surrogateDiagonalTailChunk000Sub001Block042Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block042Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block042Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block042Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block042Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block042Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block042Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block042HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block042Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block042Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block042Part000
    + surrogateDiagTailX0RatChunk000Sub001Block042Part001
    + surrogateDiagTailX0RatChunk000Sub001Block042Part002
    + surrogateDiagTailX0RatChunk000Sub001Block042Part003
    + surrogateDiagTailX0RatChunk000Sub001Block042Part004
    + surrogateDiagTailX0RatChunk000Sub001Block042Part005
    + surrogateDiagTailX0RatChunk000Sub001Block042Part006
    + surrogateDiagTailX0RatChunk000Sub001Block042Part007
    + surrogateDiagTailX0RatChunk000Sub001Block042Part008
    + surrogateDiagTailX0RatChunk000Sub001Block042Part009

def surrogateDiagonalTailChunk000Sub001Block042MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block042Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block042Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block042Part010
    + surrogateDiagTailX0RatChunk000Sub001Block042Part011
    + surrogateDiagTailX0RatChunk000Sub001Block042Part012
    + surrogateDiagTailX0RatChunk000Sub001Block042Part013
    + surrogateDiagTailX0RatChunk000Sub001Block042Part014
    + surrogateDiagTailX0RatChunk000Sub001Block042Part015
    + surrogateDiagTailX0RatChunk000Sub001Block042Part016
    + surrogateDiagTailX0RatChunk000Sub001Block042Part017
    + surrogateDiagTailX0RatChunk000Sub001Block042Part018
    + surrogateDiagTailX0RatChunk000Sub001Block042Part019

def surrogateDiagonalTailChunk000Sub001Block042TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block042Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block042Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block042Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block042Part020
    + surrogateDiagTailX0RatChunk000Sub001Block042Part021
    + surrogateDiagTailX0RatChunk000Sub001Block042Part022
    + surrogateDiagTailX0RatChunk000Sub001Block042Part023
    + surrogateDiagTailX0RatChunk000Sub001Block042Part024

def surrogateDiagonalTailChunk000Sub001Block042Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block042HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block042MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block042TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block042 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block042Part000
    + surrogateDiagTailX0RatChunk000Sub001Block042Part001
    + surrogateDiagTailX0RatChunk000Sub001Block042Part002
    + surrogateDiagTailX0RatChunk000Sub001Block042Part003
    + surrogateDiagTailX0RatChunk000Sub001Block042Part004
    + surrogateDiagTailX0RatChunk000Sub001Block042Part005
    + surrogateDiagTailX0RatChunk000Sub001Block042Part006
    + surrogateDiagTailX0RatChunk000Sub001Block042Part007
    + surrogateDiagTailX0RatChunk000Sub001Block042Part008
    + surrogateDiagTailX0RatChunk000Sub001Block042Part009
    + surrogateDiagTailX0RatChunk000Sub001Block042Part010
    + surrogateDiagTailX0RatChunk000Sub001Block042Part011
    + surrogateDiagTailX0RatChunk000Sub001Block042Part012
    + surrogateDiagTailX0RatChunk000Sub001Block042Part013
    + surrogateDiagTailX0RatChunk000Sub001Block042Part014
    + surrogateDiagTailX0RatChunk000Sub001Block042Part015
    + surrogateDiagTailX0RatChunk000Sub001Block042Part016
    + surrogateDiagTailX0RatChunk000Sub001Block042Part017
    + surrogateDiagTailX0RatChunk000Sub001Block042Part018
    + surrogateDiagTailX0RatChunk000Sub001Block042Part019
    + surrogateDiagTailX0RatChunk000Sub001Block042Part020
    + surrogateDiagTailX0RatChunk000Sub001Block042Part021
    + surrogateDiagTailX0RatChunk000Sub001Block042Part022
    + surrogateDiagTailX0RatChunk000Sub001Block042Part023
    + surrogateDiagTailX0RatChunk000Sub001Block042Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block042_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block042Head + surrogateDiagTailX0RatChunk000Sub001Block042Mid + surrogateDiagTailX0RatChunk000Sub001Block042Tail =
      surrogateDiagTailX0RatChunk000Sub001Block042 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block042Head surrogateDiagTailX0RatChunk000Sub001Block042Mid surrogateDiagTailX0RatChunk000Sub001Block042Tail surrogateDiagTailX0RatChunk000Sub001Block042
  ring

def SurrogateDiagonalTailChunk000Sub001Block042HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block042HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block042Head

def SurrogateDiagonalTailChunk000Sub001Block042MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block042MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block042Mid

def SurrogateDiagonalTailChunk000Sub001Block042TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block042TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block042Tail

theorem surrogateDiagonalTailChunk000Sub001Block042_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block042HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block042MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block042TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block042Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block042 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block042HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block042MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block042TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block042Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block042_eq_head_add_mid_add_tail

/-- Block 043 covers tail-support indices [6075,6100) and q from 10037 to 10079. -/

def TailChunk000Sub001Block043Part000SupportExplicit : Finset ℕ :=
  ([10037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part000 : ℚ :=
  (1574083890625 : ℚ) / 6341755264883249952

def SurrogateDiagonalTailChunk000Sub001Block043Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10037
    = surrogateDiagTailX0RatChunk000Sub001Block043Part000

theorem surrogateDiagonalTailChunk000Sub001Block043Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part000] using hcert

def TailChunk000Sub001Block043Part001SupportExplicit : Finset ℕ :=
  ([10038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part001 : ℚ :=
  (892513690675 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub001Block043Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10038
    = surrogateDiagTailX0RatChunk000Sub001Block043Part001

theorem surrogateDiagonalTailChunk000Sub001Block043Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part001] using hcert

def TailChunk000Sub001Block043Part002SupportExplicit : Finset ℕ :=
  ([10039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part002 : ℚ :=
  (1574711265625 : ℚ) / 6346811981677830642

def SurrogateDiagonalTailChunk000Sub001Block043Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10039
    = surrogateDiagTailX0RatChunk000Sub001Block043Part002

theorem surrogateDiagonalTailChunk000Sub001Block043Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part002] using hcert

def TailChunk000Sub001Block043Part003SupportExplicit : Finset ℕ :=
  ([10041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part003 : ℚ :=
  (2799553665325 : ℚ) / 5014765022560261248

def SurrogateDiagonalTailChunk000Sub001Block043Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10041
    = surrogateDiagTailX0RatChunk000Sub001Block043Part003

theorem surrogateDiagonalTailChunk000Sub001Block043Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part003] using hcert

def TailChunk000Sub001Block043Part004SupportExplicit : Finset ℕ :=
  ([10042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part004 : ℚ :=
  (630261025 : ℚ) / 635187172192032

def SurrogateDiagonalTailChunk000Sub001Block043Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10042
    = surrogateDiagTailX0RatChunk000Sub001Block043Part004

theorem surrogateDiagonalTailChunk000Sub001Block043Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part004] using hcert

def TailChunk000Sub001Block043Part005SupportExplicit : Finset ℕ :=
  ([10046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part005 : ℚ :=
  (394227015625 : ℚ) / 397625017348059282

def SurrogateDiagonalTailChunk000Sub001Block043Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10046
    = surrogateDiagTailX0RatChunk000Sub001Block043Part005

theorem surrogateDiagonalTailChunk000Sub001Block043Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part005] using hcert

def TailChunk000Sub001Block043Part006SupportExplicit : Finset ℕ :=
  ([10047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part006 : ℚ :=
  (322064952425 : ℚ) / 483683275181654016

def SurrogateDiagonalTailChunk000Sub001Block043Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10047
    = surrogateDiagTailX0RatChunk000Sub001Block043Part006

theorem surrogateDiagonalTailChunk000Sub001Block043Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part006] using hcert

def TailChunk000Sub001Block043Part007SupportExplicit : Finset ℕ :=
  ([10049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part007 : ℚ :=
  (5591943919375 : ℚ) / 18417091442543198208

def SurrogateDiagonalTailChunk000Sub001Block043Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10049
    = surrogateDiagTailX0RatChunk000Sub001Block043Part007

theorem surrogateDiagonalTailChunk000Sub001Block043Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part007] using hcert

def TailChunk000Sub001Block043Part008SupportExplicit : Finset ℕ :=
  ([10054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part008 : ℚ :=
  (4713709 : ℚ) / 3556416741120

def SurrogateDiagonalTailChunk000Sub001Block043Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10054
    = surrogateDiagTailX0RatChunk000Sub001Block043Part008

theorem surrogateDiagonalTailChunk000Sub001Block043Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part008] using hcert

def TailChunk000Sub001Block043Part009SupportExplicit : Finset ℕ :=
  ([10055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part009 : ℚ :=
  (181882793737 : ℚ) / 417937215785011200

def SurrogateDiagonalTailChunk000Sub001Block043Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10055
    = surrogateDiagTailX0RatChunk000Sub001Block043Part009

theorem surrogateDiagonalTailChunk000Sub001Block043Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part009] using hcert

def TailChunk000Sub001Block043Part010SupportExplicit : Finset ℕ :=
  ([10057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part010 : ℚ :=
  (438152054675 : ℚ) / 1685394616989253632

def SurrogateDiagonalTailChunk000Sub001Block043Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10057
    = surrogateDiagTailX0RatChunk000Sub001Block043Part010

theorem surrogateDiagonalTailChunk000Sub001Block043Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part010] using hcert

def TailChunk000Sub001Block043Part011SupportExplicit : Finset ℕ :=
  ([10058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part011 : ℚ :=
  (766380149375 : ℚ) / 706726947052705344

def SurrogateDiagonalTailChunk000Sub001Block043Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10058
    = surrogateDiagTailX0RatChunk000Sub001Block043Part011

theorem surrogateDiagonalTailChunk000Sub001Block043Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part011] using hcert

def TailChunk000Sub001Block043Part012SupportExplicit : Finset ℕ :=
  ([10059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part012 : ℚ :=
  (2331401027275 : ℚ) / 2706845259990878208

def SurrogateDiagonalTailChunk000Sub001Block043Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10059
    = surrogateDiagTailX0RatChunk000Sub001Block043Part012

theorem surrogateDiagonalTailChunk000Sub001Block043Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part012] using hcert

def TailChunk000Sub001Block043Part013SupportExplicit : Finset ℕ :=
  ([10061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part013 : ℚ :=
  (2530593025 : ℚ) / 10244217086690592

def SurrogateDiagonalTailChunk000Sub001Block043Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10061
    = surrogateDiagTailX0RatChunk000Sub001Block043Part013

theorem surrogateDiagonalTailChunk000Sub001Block043Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part013] using hcert

def TailChunk000Sub001Block043Part014SupportExplicit : Finset ℕ :=
  ([10063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part014 : ℚ :=
  (5980414757575 : ℚ) / 22027407157347207168

def SurrogateDiagonalTailChunk000Sub001Block043Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10063
    = surrogateDiagTailX0RatChunk000Sub001Block043Part014

theorem surrogateDiagonalTailChunk000Sub001Block043Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part014] using hcert

def TailChunk000Sub001Block043Part015SupportExplicit : Finset ℕ :=
  ([10065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part015 : ℚ :=
  (3582881909 : ℚ) / 2654738841600000

def SurrogateDiagonalTailChunk000Sub001Block043Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10065
    = surrogateDiagTailX0RatChunk000Sub001Block043Part015

theorem surrogateDiagonalTailChunk000Sub001Block043Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part015] using hcert

def TailChunk000Sub001Block043Part016SupportExplicit : Finset ℕ :=
  ([10066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part016 : ℚ :=
  (75299629825 : ℚ) / 47847266563484736

def SurrogateDiagonalTailChunk000Sub001Block043Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10066
    = surrogateDiagTailX0RatChunk000Sub001Block043Part016

theorem surrogateDiagonalTailChunk000Sub001Block043Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part016] using hcert

def TailChunk000Sub001Block043Part017SupportExplicit : Finset ℕ :=
  ([10067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part017 : ℚ :=
  (1583507640625 : ℚ) / 6417924027399061842

def SurrogateDiagonalTailChunk000Sub001Block043Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10067
    = surrogateDiagTailX0RatChunk000Sub001Block043Part017

theorem surrogateDiagonalTailChunk000Sub001Block043Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part017] using hcert

def TailChunk000Sub001Block043Part018SupportExplicit : Finset ℕ :=
  ([10069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part018 : ℚ :=
  (1584136890625 : ℚ) / 6423026222538192672

def SurrogateDiagonalTailChunk000Sub001Block043Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10069
    = surrogateDiagTailX0RatChunk000Sub001Block043Part018

theorem surrogateDiagonalTailChunk000Sub001Block043Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part018] using hcert

def TailChunk000Sub001Block043Part019SupportExplicit : Finset ℕ :=
  ([10070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part019 : ℚ :=
  (147259322975 : ℚ) / 61415816804499456

def SurrogateDiagonalTailChunk000Sub001Block043Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10070
    = surrogateDiagTailX0RatChunk000Sub001Block043Part019

theorem surrogateDiagonalTailChunk000Sub001Block043Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part019] using hcert

def TailChunk000Sub001Block043Part020SupportExplicit : Finset ℕ :=
  ([10073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part020 : ℚ :=
  (307098099175 : ℚ) / 866058885829777608

def SurrogateDiagonalTailChunk000Sub001Block043Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10073
    = surrogateDiagTailX0RatChunk000Sub001Block043Part020

theorem surrogateDiagonalTailChunk000Sub001Block043Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part020] using hcert

def TailChunk000Sub001Block043Part021SupportExplicit : Finset ℕ :=
  ([10074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part021 : ℚ :=
  (498036815225 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub001Block043Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10074
    = surrogateDiagTailX0RatChunk000Sub001Block043Part021

theorem surrogateDiagonalTailChunk000Sub001Block043Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part021] using hcert

def TailChunk000Sub001Block043Part022SupportExplicit : Finset ℕ :=
  ([10077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part022 : ℚ :=
  (881247477925 : ℚ) / 1271773049298069792

def SurrogateDiagonalTailChunk000Sub001Block043Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10077
    = surrogateDiagTailX0RatChunk000Sub001Block043Part022

theorem surrogateDiagonalTailChunk000Sub001Block043Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part022] using hcert

def TailChunk000Sub001Block043Part023SupportExplicit : Finset ℕ :=
  ([10078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part023 : ℚ :=
  (396742515625 : ℚ) / 402716589415650642

def SurrogateDiagonalTailChunk000Sub001Block043Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10078
    = surrogateDiagTailX0RatChunk000Sub001Block043Part023

theorem surrogateDiagonalTailChunk000Sub001Block043Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part023] using hcert

def TailChunk000Sub001Block043Part024SupportExplicit : Finset ℕ :=
  ([10079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block043Part024 : ℚ :=
  (1587285015625 : ℚ) / 6448582845611796882

def SurrogateDiagonalTailChunk000Sub001Block043Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10079
    = surrogateDiagTailX0RatChunk000Sub001Block043Part024

theorem surrogateDiagonalTailChunk000Sub001Block043Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block043Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block043Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block043Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block043Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block043Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block043Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block043HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block043Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block043Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block043Part000
    + surrogateDiagTailX0RatChunk000Sub001Block043Part001
    + surrogateDiagTailX0RatChunk000Sub001Block043Part002
    + surrogateDiagTailX0RatChunk000Sub001Block043Part003
    + surrogateDiagTailX0RatChunk000Sub001Block043Part004
    + surrogateDiagTailX0RatChunk000Sub001Block043Part005
    + surrogateDiagTailX0RatChunk000Sub001Block043Part006
    + surrogateDiagTailX0RatChunk000Sub001Block043Part007
    + surrogateDiagTailX0RatChunk000Sub001Block043Part008
    + surrogateDiagTailX0RatChunk000Sub001Block043Part009

def surrogateDiagonalTailChunk000Sub001Block043MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block043Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block043Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block043Part010
    + surrogateDiagTailX0RatChunk000Sub001Block043Part011
    + surrogateDiagTailX0RatChunk000Sub001Block043Part012
    + surrogateDiagTailX0RatChunk000Sub001Block043Part013
    + surrogateDiagTailX0RatChunk000Sub001Block043Part014
    + surrogateDiagTailX0RatChunk000Sub001Block043Part015
    + surrogateDiagTailX0RatChunk000Sub001Block043Part016
    + surrogateDiagTailX0RatChunk000Sub001Block043Part017
    + surrogateDiagTailX0RatChunk000Sub001Block043Part018
    + surrogateDiagTailX0RatChunk000Sub001Block043Part019

def surrogateDiagonalTailChunk000Sub001Block043TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block043Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block043Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block043Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block043Part020
    + surrogateDiagTailX0RatChunk000Sub001Block043Part021
    + surrogateDiagTailX0RatChunk000Sub001Block043Part022
    + surrogateDiagTailX0RatChunk000Sub001Block043Part023
    + surrogateDiagTailX0RatChunk000Sub001Block043Part024

def surrogateDiagonalTailChunk000Sub001Block043Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block043HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block043MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block043TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block043 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block043Part000
    + surrogateDiagTailX0RatChunk000Sub001Block043Part001
    + surrogateDiagTailX0RatChunk000Sub001Block043Part002
    + surrogateDiagTailX0RatChunk000Sub001Block043Part003
    + surrogateDiagTailX0RatChunk000Sub001Block043Part004
    + surrogateDiagTailX0RatChunk000Sub001Block043Part005
    + surrogateDiagTailX0RatChunk000Sub001Block043Part006
    + surrogateDiagTailX0RatChunk000Sub001Block043Part007
    + surrogateDiagTailX0RatChunk000Sub001Block043Part008
    + surrogateDiagTailX0RatChunk000Sub001Block043Part009
    + surrogateDiagTailX0RatChunk000Sub001Block043Part010
    + surrogateDiagTailX0RatChunk000Sub001Block043Part011
    + surrogateDiagTailX0RatChunk000Sub001Block043Part012
    + surrogateDiagTailX0RatChunk000Sub001Block043Part013
    + surrogateDiagTailX0RatChunk000Sub001Block043Part014
    + surrogateDiagTailX0RatChunk000Sub001Block043Part015
    + surrogateDiagTailX0RatChunk000Sub001Block043Part016
    + surrogateDiagTailX0RatChunk000Sub001Block043Part017
    + surrogateDiagTailX0RatChunk000Sub001Block043Part018
    + surrogateDiagTailX0RatChunk000Sub001Block043Part019
    + surrogateDiagTailX0RatChunk000Sub001Block043Part020
    + surrogateDiagTailX0RatChunk000Sub001Block043Part021
    + surrogateDiagTailX0RatChunk000Sub001Block043Part022
    + surrogateDiagTailX0RatChunk000Sub001Block043Part023
    + surrogateDiagTailX0RatChunk000Sub001Block043Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block043_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block043Head + surrogateDiagTailX0RatChunk000Sub001Block043Mid + surrogateDiagTailX0RatChunk000Sub001Block043Tail =
      surrogateDiagTailX0RatChunk000Sub001Block043 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block043Head surrogateDiagTailX0RatChunk000Sub001Block043Mid surrogateDiagTailX0RatChunk000Sub001Block043Tail surrogateDiagTailX0RatChunk000Sub001Block043
  ring

def SurrogateDiagonalTailChunk000Sub001Block043HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block043HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block043Head

def SurrogateDiagonalTailChunk000Sub001Block043MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block043MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block043Mid

def SurrogateDiagonalTailChunk000Sub001Block043TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block043TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block043Tail

theorem surrogateDiagonalTailChunk000Sub001Block043_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block043HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block043MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block043TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block043Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block043 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block043HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block043MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block043TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block043Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block043_eq_head_add_mid_add_tail

/-- Block 044 covers tail-support indices [6100,6125) and q from 10081 to 10122. -/

def TailChunk000Sub001Block044Part000SupportExplicit : Finset ℕ :=
  ([10081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part000 : ℚ :=
  (961088408625 : ℚ) / 3354612539366309888

def SurrogateDiagonalTailChunk000Sub001Block044Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10081
    = surrogateDiagTailX0RatChunk000Sub001Block044Part000

theorem surrogateDiagonalTailChunk000Sub001Block044Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part000] using hcert

def TailChunk000Sub001Block044Part001SupportExplicit : Finset ℕ :=
  ([10083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part001 : ℚ :=
  (70583786669 : ℚ) / 101984447338905600

def SurrogateDiagonalTailChunk000Sub001Block044Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10083
    = surrogateDiagTailX0RatChunk000Sub001Block044Part001

theorem surrogateDiagonalTailChunk000Sub001Block044Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part001] using hcert

def TailChunk000Sub001Block044Part002SupportExplicit : Finset ℕ :=
  ([10085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part002 : ℚ :=
  (653464224475 : ℚ) / 1510535357156818944

def SurrogateDiagonalTailChunk000Sub001Block044Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10085
    = surrogateDiagTailX0RatChunk000Sub001Block044Part002

theorem surrogateDiagonalTailChunk000Sub001Block044Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part002] using hcert

def TailChunk000Sub001Block044Part003SupportExplicit : Finset ℕ :=
  ([10087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part003 : ℚ :=
  (19210048301 : ℚ) / 41136065568000000

def SurrogateDiagonalTailChunk000Sub001Block044Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10087
    = surrogateDiagTailX0RatChunk000Sub001Block044Part003

theorem surrogateDiagonalTailChunk000Sub001Block044Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part003] using hcert

def TailChunk000Sub001Block044Part004SupportExplicit : Finset ℕ :=
  ([10090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part004 : ℚ :=
  (635792007875 : ℚ) / 330429609378054144

def SurrogateDiagonalTailChunk000Sub001Block044Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10090
    = surrogateDiagTailX0RatChunk000Sub001Block044Part004

theorem surrogateDiagonalTailChunk000Sub001Block044Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part004] using hcert

def TailChunk000Sub001Block044Part005SupportExplicit : Finset ℕ :=
  ([10091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part005 : ℚ :=
  (2545707025 : ℚ) / 10366962203455122

def SurrogateDiagonalTailChunk000Sub001Block044Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10091
    = surrogateDiagTailX0RatChunk000Sub001Block044Part005

theorem surrogateDiagonalTailChunk000Sub001Block044Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part005] using hcert

def TailChunk000Sub001Block044Part006SupportExplicit : Finset ℕ :=
  ([10093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part006 : ℚ :=
  (1591697640625 : ℚ) / 6484490150676954912

def SurrogateDiagonalTailChunk000Sub001Block044Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10093
    = surrogateDiagTailX0RatChunk000Sub001Block044Part006

theorem surrogateDiagonalTailChunk000Sub001Block044Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part006] using hcert

def TailChunk000Sub001Block044Part007SupportExplicit : Finset ℕ :=
  ([10095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part007 : ℚ :=
  (2599530935425 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk000Sub001Block044Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10095
    = surrogateDiagTailX0RatChunk000Sub001Block044Part007

theorem surrogateDiagonalTailChunk000Sub001Block044Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part007] using hcert

def TailChunk000Sub001Block044Part008SupportExplicit : Finset ℕ :=
  ([10097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part008 : ℚ :=
  (165080604575 : ℚ) / 598840995182826528

def SurrogateDiagonalTailChunk000Sub001Block044Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10097
    = surrogateDiagTailX0RatChunk000Sub001Block044Part008

theorem surrogateDiagonalTailChunk000Sub001Block044Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part008] using hcert

def TailChunk000Sub001Block044Part009SupportExplicit : Finset ℕ :=
  ([10099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part009 : ℚ :=
  (1593590640625 : ℚ) / 6499924812465499602

def SurrogateDiagonalTailChunk000Sub001Block044Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10099
    = surrogateDiagTailX0RatChunk000Sub001Block044Part009

theorem surrogateDiagonalTailChunk000Sub001Block044Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part009] using hcert

def TailChunk000Sub001Block044Part010SupportExplicit : Finset ℕ :=
  ([10101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part010 : ℚ :=
  (796462996975 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub001Block044Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10101
    = surrogateDiagTailX0RatChunk000Sub001Block044Part010

theorem surrogateDiagonalTailChunk000Sub001Block044Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part010] using hcert

def TailChunk000Sub001Block044Part011SupportExplicit : Finset ℕ :=
  ([10102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part011 : ℚ :=
  (25512601 : ℚ) / 26020303270050

def SurrogateDiagonalTailChunk000Sub001Block044Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10102
    = surrogateDiagTailX0RatChunk000Sub001Block044Part011

theorem surrogateDiagonalTailChunk000Sub001Block044Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part011] using hcert

def TailChunk000Sub001Block044Part012SupportExplicit : Finset ℕ :=
  ([10103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block044Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10103
    = surrogateDiagTailX0RatChunk000Sub001Block044Part012

theorem surrogateDiagonalTailChunk000Sub001Block044Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part012] using hcert

def TailChunk000Sub001Block044Part013SupportExplicit : Finset ℕ :=
  ([10105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part013 : ℚ :=
  (573825855025 : ℚ) / 8918571789927088128

def SurrogateDiagonalTailChunk000Sub001Block044Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10105
    = surrogateDiagTailX0RatChunk000Sub001Block044Part013

theorem surrogateDiagonalTailChunk000Sub001Block044Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part013] using hcert

def TailChunk000Sub001Block044Part014SupportExplicit : Finset ℕ :=
  ([10106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part014 : ℚ :=
  (12280320563 : ℚ) / 11159941625216640

def SurrogateDiagonalTailChunk000Sub001Block044Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10106
    = surrogateDiagTailX0RatChunk000Sub001Block044Part014

theorem surrogateDiagonalTailChunk000Sub001Block044Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part014] using hcert

def TailChunk000Sub001Block044Part015SupportExplicit : Finset ℕ :=
  ([10109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part015 : ℚ :=
  (20883743 : ℚ) / 1392795641027520

def SurrogateDiagonalTailChunk000Sub001Block044Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10109
    = surrogateDiagTailX0RatChunk000Sub001Block044Part015

theorem surrogateDiagonalTailChunk000Sub001Block044Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part015] using hcert

def TailChunk000Sub001Block044Part016SupportExplicit : Finset ℕ :=
  ([10110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part016 : ℚ :=
  (121340352325 : ℚ) / 18648584656257024

def SurrogateDiagonalTailChunk000Sub001Block044Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10110
    = surrogateDiagTailX0RatChunk000Sub001Block044Part016

theorem surrogateDiagonalTailChunk000Sub001Block044Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part016] using hcert

def TailChunk000Sub001Block044Part017SupportExplicit : Finset ℕ :=
  ([10111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block044Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10111
    = surrogateDiagTailX0RatChunk000Sub001Block044Part017

theorem surrogateDiagonalTailChunk000Sub001Block044Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part017] using hcert

def TailChunk000Sub001Block044Part018SupportExplicit : Finset ℕ :=
  ([10113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part018 : ℚ :=
  (2841725413 : ℚ) / 20640795751283520

def SurrogateDiagonalTailChunk000Sub001Block044Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10113
    = surrogateDiagTailX0RatChunk000Sub001Block044Part018

theorem surrogateDiagonalTailChunk000Sub001Block044Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part018] using hcert

def TailChunk000Sub001Block044Part019SupportExplicit : Finset ℕ :=
  ([10114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part019 : ℚ :=
  (735921029675 : ℚ) / 587555302224052224

def SurrogateDiagonalTailChunk000Sub001Block044Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10114
    = surrogateDiagTailX0RatChunk000Sub001Block044Part019

theorem surrogateDiagonalTailChunk000Sub001Block044Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part019] using hcert

def TailChunk000Sub001Block044Part020SupportExplicit : Finset ℕ :=
  ([10117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part020 : ℚ :=
  (49504343 : ℚ) / 17792372763000000

def SurrogateDiagonalTailChunk000Sub001Block044Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10117
    = surrogateDiagTailX0RatChunk000Sub001Block044Part020

theorem surrogateDiagonalTailChunk000Sub001Block044Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part020] using hcert

def TailChunk000Sub001Block044Part021SupportExplicit : Finset ℕ :=
  ([10118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part021 : ℚ :=
  (399898140625 : ℚ) / 409149634537004562

def SurrogateDiagonalTailChunk000Sub001Block044Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10118
    = surrogateDiagTailX0RatChunk000Sub001Block044Part021

theorem surrogateDiagonalTailChunk000Sub001Block044Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part021] using hcert

def TailChunk000Sub001Block044Part022SupportExplicit : Finset ℕ :=
  ([10119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part022 : ℚ :=
  (22227315725 : ℚ) / 161639361792396864

def SurrogateDiagonalTailChunk000Sub001Block044Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10119
    = surrogateDiagTailX0RatChunk000Sub001Block044Part022

theorem surrogateDiagonalTailChunk000Sub001Block044Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part022] using hcert

def TailChunk000Sub001Block044Part023SupportExplicit : Finset ℕ :=
  ([10121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part023 : ℚ :=
  (114421049875 : ℚ) / 22541144343221403648

def SurrogateDiagonalTailChunk000Sub001Block044Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10121
    = surrogateDiagTailX0RatChunk000Sub001Block044Part023

theorem surrogateDiagonalTailChunk000Sub001Block044Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part023] using hcert

def TailChunk000Sub001Block044Part024SupportExplicit : Finset ℕ :=
  ([10122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block044Part024 : ℚ :=
  (485831 : ℚ) / 91729428480

def SurrogateDiagonalTailChunk000Sub001Block044Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10122
    = surrogateDiagTailX0RatChunk000Sub001Block044Part024

theorem surrogateDiagonalTailChunk000Sub001Block044Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block044Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block044Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block044Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block044Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block044Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block044Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block044HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block044Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block044Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block044Part000
    + surrogateDiagTailX0RatChunk000Sub001Block044Part001
    + surrogateDiagTailX0RatChunk000Sub001Block044Part002
    + surrogateDiagTailX0RatChunk000Sub001Block044Part003
    + surrogateDiagTailX0RatChunk000Sub001Block044Part004
    + surrogateDiagTailX0RatChunk000Sub001Block044Part005
    + surrogateDiagTailX0RatChunk000Sub001Block044Part006
    + surrogateDiagTailX0RatChunk000Sub001Block044Part007
    + surrogateDiagTailX0RatChunk000Sub001Block044Part008
    + surrogateDiagTailX0RatChunk000Sub001Block044Part009

def surrogateDiagonalTailChunk000Sub001Block044MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block044Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block044Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block044Part010
    + surrogateDiagTailX0RatChunk000Sub001Block044Part011
    + surrogateDiagTailX0RatChunk000Sub001Block044Part012
    + surrogateDiagTailX0RatChunk000Sub001Block044Part013
    + surrogateDiagTailX0RatChunk000Sub001Block044Part014
    + surrogateDiagTailX0RatChunk000Sub001Block044Part015
    + surrogateDiagTailX0RatChunk000Sub001Block044Part016
    + surrogateDiagTailX0RatChunk000Sub001Block044Part017
    + surrogateDiagTailX0RatChunk000Sub001Block044Part018
    + surrogateDiagTailX0RatChunk000Sub001Block044Part019

def surrogateDiagonalTailChunk000Sub001Block044TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block044Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block044Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block044Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block044Part020
    + surrogateDiagTailX0RatChunk000Sub001Block044Part021
    + surrogateDiagTailX0RatChunk000Sub001Block044Part022
    + surrogateDiagTailX0RatChunk000Sub001Block044Part023
    + surrogateDiagTailX0RatChunk000Sub001Block044Part024

def surrogateDiagonalTailChunk000Sub001Block044Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block044HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block044MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block044TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block044 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block044Part000
    + surrogateDiagTailX0RatChunk000Sub001Block044Part001
    + surrogateDiagTailX0RatChunk000Sub001Block044Part002
    + surrogateDiagTailX0RatChunk000Sub001Block044Part003
    + surrogateDiagTailX0RatChunk000Sub001Block044Part004
    + surrogateDiagTailX0RatChunk000Sub001Block044Part005
    + surrogateDiagTailX0RatChunk000Sub001Block044Part006
    + surrogateDiagTailX0RatChunk000Sub001Block044Part007
    + surrogateDiagTailX0RatChunk000Sub001Block044Part008
    + surrogateDiagTailX0RatChunk000Sub001Block044Part009
    + surrogateDiagTailX0RatChunk000Sub001Block044Part010
    + surrogateDiagTailX0RatChunk000Sub001Block044Part011
    + surrogateDiagTailX0RatChunk000Sub001Block044Part012
    + surrogateDiagTailX0RatChunk000Sub001Block044Part013
    + surrogateDiagTailX0RatChunk000Sub001Block044Part014
    + surrogateDiagTailX0RatChunk000Sub001Block044Part015
    + surrogateDiagTailX0RatChunk000Sub001Block044Part016
    + surrogateDiagTailX0RatChunk000Sub001Block044Part017
    + surrogateDiagTailX0RatChunk000Sub001Block044Part018
    + surrogateDiagTailX0RatChunk000Sub001Block044Part019
    + surrogateDiagTailX0RatChunk000Sub001Block044Part020
    + surrogateDiagTailX0RatChunk000Sub001Block044Part021
    + surrogateDiagTailX0RatChunk000Sub001Block044Part022
    + surrogateDiagTailX0RatChunk000Sub001Block044Part023
    + surrogateDiagTailX0RatChunk000Sub001Block044Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block044_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block044Head + surrogateDiagTailX0RatChunk000Sub001Block044Mid + surrogateDiagTailX0RatChunk000Sub001Block044Tail =
      surrogateDiagTailX0RatChunk000Sub001Block044 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block044Head surrogateDiagTailX0RatChunk000Sub001Block044Mid surrogateDiagTailX0RatChunk000Sub001Block044Tail surrogateDiagTailX0RatChunk000Sub001Block044
  ring

def SurrogateDiagonalTailChunk000Sub001Block044HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block044HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block044Head

def SurrogateDiagonalTailChunk000Sub001Block044MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block044MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block044Mid

def SurrogateDiagonalTailChunk000Sub001Block044TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block044TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block044Tail

theorem surrogateDiagonalTailChunk000Sub001Block044_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block044HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block044MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block044TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block044Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block044 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block044HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block044MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block044TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block044Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block044_eq_head_add_mid_add_tail

/-- Block 045 covers tail-support indices [6125,6150) and q from 10123 to 10162. -/

def TailChunk000Sub001Block045Part000SupportExplicit : Finset ℕ :=
  ([10123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part000 : ℚ :=
  (149450009 : ℚ) / 47652384007887360

def SurrogateDiagonalTailChunk000Sub001Block045Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10123
    = surrogateDiagTailX0RatChunk000Sub001Block045Part000

theorem surrogateDiagonalTailChunk000Sub001Block045Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part000] using hcert

def TailChunk000Sub001Block045Part001SupportExplicit : Finset ℕ :=
  ([10126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part001 : ℚ :=
  (31130693213 : ℚ) / 29303349546009600

def SurrogateDiagonalTailChunk000Sub001Block045Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10126
    = surrogateDiagTailX0RatChunk000Sub001Block045Part001

theorem surrogateDiagonalTailChunk000Sub001Block045Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part001] using hcert

def TailChunk000Sub001Block045Part002SupportExplicit : Finset ℕ :=
  ([10127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part002 : ℚ :=
  (5777601191 : ℚ) / 185789243090534400

def SurrogateDiagonalTailChunk000Sub001Block045Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10127
    = surrogateDiagTailX0RatChunk000Sub001Block045Part002

theorem surrogateDiagonalTailChunk000Sub001Block045Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part002] using hcert

def TailChunk000Sub001Block045Part003SupportExplicit : Finset ℕ :=
  ([10129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part003 : ℚ :=
  (7291936225 : ℚ) / 262368246299988672

def SurrogateDiagonalTailChunk000Sub001Block045Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10129
    = surrogateDiagTailX0RatChunk000Sub001Block045Part003

theorem surrogateDiagonalTailChunk000Sub001Block045Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part003] using hcert

def TailChunk000Sub001Block045Part004SupportExplicit : Finset ℕ :=
  ([10130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part004 : ℚ :=
  (640843017875 : ℚ) / 335705826215215104

def SurrogateDiagonalTailChunk000Sub001Block045Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10130
    = surrogateDiagTailX0RatChunk000Sub001Block045Part004

theorem surrogateDiagonalTailChunk000Sub001Block045Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part004] using hcert

def TailChunk000Sub001Block045Part005SupportExplicit : Finset ℕ :=
  ([10131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part005 : ℚ :=
  (10460794607 : ℚ) / 46770421525862400

def SurrogateDiagonalTailChunk000Sub001Block045Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10131
    = surrogateDiagTailX0RatChunk000Sub001Block045Part005

theorem surrogateDiagonalTailChunk000Sub001Block045Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part005] using hcert

def TailChunk000Sub001Block045Part006SupportExplicit : Finset ℕ :=
  ([10133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block045Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10133
    = surrogateDiagTailX0RatChunk000Sub001Block045Part006

theorem surrogateDiagonalTailChunk000Sub001Block045Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part006] using hcert

def TailChunk000Sub001Block045Part007SupportExplicit : Finset ℕ :=
  ([10135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part007 : ℚ :=
  (192642224425 : ℚ) / 2696277558078239232

def SurrogateDiagonalTailChunk000Sub001Block045Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10135
    = surrogateDiagTailX0RatChunk000Sub001Block045Part007

theorem surrogateDiagonalTailChunk000Sub001Block045Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part007] using hcert

def TailChunk000Sub001Block045Part008SupportExplicit : Finset ℕ :=
  ([10137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part008 : ℚ :=
  (55818319693 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub001Block045Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10137
    = surrogateDiagTailX0RatChunk000Sub001Block045Part008

theorem surrogateDiagonalTailChunk000Sub001Block045Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part008] using hcert

def TailChunk000Sub001Block045Part009SupportExplicit : Finset ℕ :=
  ([10138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part009 : ℚ :=
  (19151334125 : ℚ) / 17738115423141888

def SurrogateDiagonalTailChunk000Sub001Block045Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10138
    = surrogateDiagTailX0RatChunk000Sub001Block045Part009

theorem surrogateDiagonalTailChunk000Sub001Block045Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part009] using hcert

def TailChunk000Sub001Block045Part010SupportExplicit : Finset ℕ :=
  ([10139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block045Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10139
    = surrogateDiagTailX0RatChunk000Sub001Block045Part010

theorem surrogateDiagonalTailChunk000Sub001Block045Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part010] using hcert

def TailChunk000Sub001Block045Part011SupportExplicit : Finset ℕ :=
  ([10141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block045Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10141
    = surrogateDiagTailX0RatChunk000Sub001Block045Part011

theorem surrogateDiagonalTailChunk000Sub001Block045Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part011] using hcert

def TailChunk000Sub001Block045Part012SupportExplicit : Finset ℕ :=
  ([10142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part012 : ℚ :=
  (729081287 : ℚ) / 559793936400000

def SurrogateDiagonalTailChunk000Sub001Block045Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10142
    = surrogateDiagTailX0RatChunk000Sub001Block045Part012

theorem surrogateDiagonalTailChunk000Sub001Block045Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part012] using hcert

def TailChunk000Sub001Block045Part013SupportExplicit : Finset ℕ :=
  ([10145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part013 : ℚ :=
  (171748565575 : ℚ) / 3609253382208454656

def SurrogateDiagonalTailChunk000Sub001Block045Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10145
    = surrogateDiagTailX0RatChunk000Sub001Block045Part013

theorem surrogateDiagonalTailChunk000Sub001Block045Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part013] using hcert

def TailChunk000Sub001Block045Part014SupportExplicit : Finset ℕ :=
  ([10146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part014 : ℚ :=
  (1004504543725 : ℚ) / 251864843341529088

def SurrogateDiagonalTailChunk000Sub001Block045Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10146
    = surrogateDiagTailX0RatChunk000Sub001Block045Part014

theorem surrogateDiagonalTailChunk000Sub001Block045Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part014] using hcert

def TailChunk000Sub001Block045Part015SupportExplicit : Finset ℕ :=
  ([10147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part015 : ℚ :=
  (16222927825 : ℚ) / 6092747762777137152

def SurrogateDiagonalTailChunk000Sub001Block045Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10147
    = surrogateDiagTailX0RatChunk000Sub001Block045Part015

theorem surrogateDiagonalTailChunk000Sub001Block045Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part015] using hcert

def TailChunk000Sub001Block045Part016SupportExplicit : Finset ℕ :=
  ([10149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part016 : ℚ :=
  (459796016375 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub001Block045Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10149
    = surrogateDiagTailX0RatChunk000Sub001Block045Part016

theorem surrogateDiagonalTailChunk000Sub001Block045Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part016] using hcert

def TailChunk000Sub001Block045Part017SupportExplicit : Finset ℕ :=
  ([10151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block045Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10151
    = surrogateDiagTailX0RatChunk000Sub001Block045Part017

theorem surrogateDiagonalTailChunk000Sub001Block045Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part017] using hcert

def TailChunk000Sub001Block045Part018SupportExplicit : Finset ℕ :=
  ([10153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part018 : ℚ :=
  (136955321 : ℚ) / 3387557376000000

def SurrogateDiagonalTailChunk000Sub001Block045Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10153
    = surrogateDiagTailX0RatChunk000Sub001Block045Part018

theorem surrogateDiagonalTailChunk000Sub001Block045Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part018] using hcert

def TailChunk000Sub001Block045Part019SupportExplicit : Finset ℕ :=
  ([10154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part019 : ℚ :=
  (402748890625 : ℚ) / 415004992452970272

def SurrogateDiagonalTailChunk000Sub001Block045Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10154
    = surrogateDiagTailX0RatChunk000Sub001Block045Part019

theorem surrogateDiagonalTailChunk000Sub001Block045Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part019] using hcert

def TailChunk000Sub001Block045Part020SupportExplicit : Finset ℕ :=
  ([10155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part020 : ℚ :=
  (1230404025475 : ℚ) / 2138816819086491648

def SurrogateDiagonalTailChunk000Sub001Block045Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10155
    = surrogateDiagTailX0RatChunk000Sub001Block045Part020

theorem surrogateDiagonalTailChunk000Sub001Block045Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part020] using hcert

def TailChunk000Sub001Block045Part021SupportExplicit : Finset ℕ :=
  ([10157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part021 : ℚ :=
  (21087361693 : ℚ) / 573012189522000000

def SurrogateDiagonalTailChunk000Sub001Block045Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10157
    = surrogateDiagTailX0RatChunk000Sub001Block045Part021

theorem surrogateDiagonalTailChunk000Sub001Block045Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part021] using hcert

def TailChunk000Sub001Block045Part022SupportExplicit : Finset ℕ :=
  ([10158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part022 : ℚ :=
  (35806625 : ℚ) / 10927987043328

def SurrogateDiagonalTailChunk000Sub001Block045Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10158
    = surrogateDiagTailX0RatChunk000Sub001Block045Part022

theorem surrogateDiagonalTailChunk000Sub001Block045Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part022] using hcert

def TailChunk000Sub001Block045Part023SupportExplicit : Finset ℕ :=
  ([10159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block045Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10159
    = surrogateDiagTailX0RatChunk000Sub001Block045Part023

theorem surrogateDiagonalTailChunk000Sub001Block045Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part023] using hcert

def TailChunk000Sub001Block045Part024SupportExplicit : Finset ℕ :=
  ([10162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block045Part024 : ℚ :=
  (645414025 : ℚ) / 666103475016192

def SurrogateDiagonalTailChunk000Sub001Block045Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10162
    = surrogateDiagTailX0RatChunk000Sub001Block045Part024

theorem surrogateDiagonalTailChunk000Sub001Block045Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block045Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block045Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block045Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block045Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block045Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block045Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block045HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block045Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block045Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block045Part000
    + surrogateDiagTailX0RatChunk000Sub001Block045Part001
    + surrogateDiagTailX0RatChunk000Sub001Block045Part002
    + surrogateDiagTailX0RatChunk000Sub001Block045Part003
    + surrogateDiagTailX0RatChunk000Sub001Block045Part004
    + surrogateDiagTailX0RatChunk000Sub001Block045Part005
    + surrogateDiagTailX0RatChunk000Sub001Block045Part006
    + surrogateDiagTailX0RatChunk000Sub001Block045Part007
    + surrogateDiagTailX0RatChunk000Sub001Block045Part008
    + surrogateDiagTailX0RatChunk000Sub001Block045Part009

def surrogateDiagonalTailChunk000Sub001Block045MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block045Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block045Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block045Part010
    + surrogateDiagTailX0RatChunk000Sub001Block045Part011
    + surrogateDiagTailX0RatChunk000Sub001Block045Part012
    + surrogateDiagTailX0RatChunk000Sub001Block045Part013
    + surrogateDiagTailX0RatChunk000Sub001Block045Part014
    + surrogateDiagTailX0RatChunk000Sub001Block045Part015
    + surrogateDiagTailX0RatChunk000Sub001Block045Part016
    + surrogateDiagTailX0RatChunk000Sub001Block045Part017
    + surrogateDiagTailX0RatChunk000Sub001Block045Part018
    + surrogateDiagTailX0RatChunk000Sub001Block045Part019

def surrogateDiagonalTailChunk000Sub001Block045TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block045Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block045Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block045Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block045Part020
    + surrogateDiagTailX0RatChunk000Sub001Block045Part021
    + surrogateDiagTailX0RatChunk000Sub001Block045Part022
    + surrogateDiagTailX0RatChunk000Sub001Block045Part023
    + surrogateDiagTailX0RatChunk000Sub001Block045Part024

def surrogateDiagonalTailChunk000Sub001Block045Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block045HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block045MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block045TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block045 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block045Part000
    + surrogateDiagTailX0RatChunk000Sub001Block045Part001
    + surrogateDiagTailX0RatChunk000Sub001Block045Part002
    + surrogateDiagTailX0RatChunk000Sub001Block045Part003
    + surrogateDiagTailX0RatChunk000Sub001Block045Part004
    + surrogateDiagTailX0RatChunk000Sub001Block045Part005
    + surrogateDiagTailX0RatChunk000Sub001Block045Part006
    + surrogateDiagTailX0RatChunk000Sub001Block045Part007
    + surrogateDiagTailX0RatChunk000Sub001Block045Part008
    + surrogateDiagTailX0RatChunk000Sub001Block045Part009
    + surrogateDiagTailX0RatChunk000Sub001Block045Part010
    + surrogateDiagTailX0RatChunk000Sub001Block045Part011
    + surrogateDiagTailX0RatChunk000Sub001Block045Part012
    + surrogateDiagTailX0RatChunk000Sub001Block045Part013
    + surrogateDiagTailX0RatChunk000Sub001Block045Part014
    + surrogateDiagTailX0RatChunk000Sub001Block045Part015
    + surrogateDiagTailX0RatChunk000Sub001Block045Part016
    + surrogateDiagTailX0RatChunk000Sub001Block045Part017
    + surrogateDiagTailX0RatChunk000Sub001Block045Part018
    + surrogateDiagTailX0RatChunk000Sub001Block045Part019
    + surrogateDiagTailX0RatChunk000Sub001Block045Part020
    + surrogateDiagTailX0RatChunk000Sub001Block045Part021
    + surrogateDiagTailX0RatChunk000Sub001Block045Part022
    + surrogateDiagTailX0RatChunk000Sub001Block045Part023
    + surrogateDiagTailX0RatChunk000Sub001Block045Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block045_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block045Head + surrogateDiagTailX0RatChunk000Sub001Block045Mid + surrogateDiagTailX0RatChunk000Sub001Block045Tail =
      surrogateDiagTailX0RatChunk000Sub001Block045 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block045Head surrogateDiagTailX0RatChunk000Sub001Block045Mid surrogateDiagTailX0RatChunk000Sub001Block045Tail surrogateDiagTailX0RatChunk000Sub001Block045
  ring

def SurrogateDiagonalTailChunk000Sub001Block045HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block045HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block045Head

def SurrogateDiagonalTailChunk000Sub001Block045MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block045MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block045Mid

def SurrogateDiagonalTailChunk000Sub001Block045TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block045TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block045Tail

theorem surrogateDiagonalTailChunk000Sub001Block045_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block045HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block045MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block045TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block045Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block045 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block045HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block045MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block045TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block045Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block045_eq_head_add_mid_add_tail

/-- Block 046 covers tail-support indices [6150,6175) and q from 10163 to 10202. -/

def TailChunk000Sub001Block046Part000SupportExplicit : Finset ℕ :=
  ([10163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block046Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10163
    = surrogateDiagTailX0RatChunk000Sub001Block046Part000

theorem surrogateDiagonalTailChunk000Sub001Block046Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part000] using hcert

def TailChunk000Sub001Block046Part001SupportExplicit : Finset ℕ :=
  ([10165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part001 : ℚ :=
  (830266492675 : ℚ) / 8483602387790757888

def SurrogateDiagonalTailChunk000Sub001Block046Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10165
    = surrogateDiagTailX0RatChunk000Sub001Block046Part001

theorem surrogateDiagonalTailChunk000Sub001Block046Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part001] using hcert

def TailChunk000Sub001Block046Part002SupportExplicit : Finset ℕ :=
  ([10166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part002 : ℚ :=
  (222933878125 : ℚ) / 132669547109941248

def SurrogateDiagonalTailChunk000Sub001Block046Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10166
    = surrogateDiagTailX0RatChunk000Sub001Block046Part002

theorem surrogateDiagonalTailChunk000Sub001Block046Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part002] using hcert

def TailChunk000Sub001Block046Part003SupportExplicit : Finset ℕ :=
  ([10167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part003 : ℚ :=
  (717577911275 : ℚ) / 2635666475088159744

def SurrogateDiagonalTailChunk000Sub001Block046Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10167
    = surrogateDiagTailX0RatChunk000Sub001Block046Part003

theorem surrogateDiagonalTailChunk000Sub001Block046Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part003] using hcert

def TailChunk000Sub001Block046Part004SupportExplicit : Finset ℕ :=
  ([10169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block046Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10169
    = surrogateDiagTailX0RatChunk000Sub001Block046Part004

theorem surrogateDiagonalTailChunk000Sub001Block046Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part004] using hcert

def TailChunk000Sub001Block046Part005SupportExplicit : Finset ℕ :=
  ([10171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part005 : ℚ :=
  (7352287075 : ℚ) / 266750084734036992

def SurrogateDiagonalTailChunk000Sub001Block046Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10171
    = surrogateDiagTailX0RatChunk000Sub001Block046Part005

theorem surrogateDiagonalTailChunk000Sub001Block046Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part005] using hcert

def TailChunk000Sub001Block046Part006SupportExplicit : Finset ℕ :=
  ([10173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part006 : ℚ :=
  (2875525411 : ℚ) / 21135164173197120

def SurrogateDiagonalTailChunk000Sub001Block046Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10173
    = surrogateDiagTailX0RatChunk000Sub001Block046Part006

theorem surrogateDiagonalTailChunk000Sub001Block046Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part006] using hcert

def TailChunk000Sub001Block046Part007SupportExplicit : Finset ℕ :=
  ([10174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part007 : ℚ :=
  (404337015625 : ℚ) / 418285000159987602

def SurrogateDiagonalTailChunk000Sub001Block046Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10174
    = surrogateDiagTailX0RatChunk000Sub001Block046Part007

theorem surrogateDiagonalTailChunk000Sub001Block046Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part007] using hcert

def TailChunk000Sub001Block046Part008SupportExplicit : Finset ℕ :=
  ([10177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block046Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10177
    = surrogateDiagTailX0RatChunk000Sub001Block046Part008

theorem surrogateDiagonalTailChunk000Sub001Block046Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part008] using hcert

def TailChunk000Sub001Block046Part009SupportExplicit : Finset ℕ :=
  ([10178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part009 : ℚ :=
  (25661544475 : ℚ) / 16671880295877312

def SurrogateDiagonalTailChunk000Sub001Block046Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10178
    = surrogateDiagTailX0RatChunk000Sub001Block046Part009

theorem surrogateDiagonalTailChunk000Sub001Block046Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part009] using hcert

def TailChunk000Sub001Block046Part010SupportExplicit : Finset ℕ :=
  ([10181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block046Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10181
    = surrogateDiagTailX0RatChunk000Sub001Block046Part010

theorem surrogateDiagonalTailChunk000Sub001Block046Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part010] using hcert

def TailChunk000Sub001Block046Part011SupportExplicit : Finset ℕ :=
  ([10182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part011 : ℚ :=
  (107928075 : ℚ) / 33095076020224

def SurrogateDiagonalTailChunk000Sub001Block046Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10182
    = surrogateDiagTailX0RatChunk000Sub001Block046Part011

theorem surrogateDiagonalTailChunk000Sub001Block046Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part011] using hcert

def TailChunk000Sub001Block046Part012SupportExplicit : Finset ℕ :=
  ([10183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part012 : ℚ :=
  (68609407725 : ℚ) / 6985383768892112896

def SurrogateDiagonalTailChunk000Sub001Block046Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10183
    = surrogateDiagTailX0RatChunk000Sub001Block046Part012

theorem surrogateDiagonalTailChunk000Sub001Block046Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part012] using hcert

def TailChunk000Sub001Block046Part013SupportExplicit : Finset ℕ :=
  ([10185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part013 : ℚ :=
  (418753806425 : ℚ) / 563698325702836224

def SurrogateDiagonalTailChunk000Sub001Block046Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10185
    = surrogateDiagTailX0RatChunk000Sub001Block046Part013

theorem surrogateDiagonalTailChunk000Sub001Block046Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part013] using hcert

def TailChunk000Sub001Block046Part014SupportExplicit : Finset ℕ :=
  ([10186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part014 : ℚ :=
  (267425929 : ℚ) / 207124785473760

def SurrogateDiagonalTailChunk000Sub001Block046Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10186
    = surrogateDiagTailX0RatChunk000Sub001Block046Part014

theorem surrogateDiagonalTailChunk000Sub001Block046Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part014] using hcert

def TailChunk000Sub001Block046Part015SupportExplicit : Finset ℕ :=
  ([10187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part015 : ℚ :=
  (2736852439 : ℚ) / 984292563404851200

def SurrogateDiagonalTailChunk000Sub001Block046Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10187
    = surrogateDiagTailX0RatChunk000Sub001Block046Part015

theorem surrogateDiagonalTailChunk000Sub001Block046Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part015] using hcert

def TailChunk000Sub001Block046Part016SupportExplicit : Finset ℕ :=
  ([10189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part016 : ℚ :=
  (1806512025 : ℚ) / 286623672879068096

def SurrogateDiagonalTailChunk000Sub001Block046Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10189
    = surrogateDiagTailX0RatChunk000Sub001Block046Part016

theorem surrogateDiagonalTailChunk000Sub001Block046Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part016] using hcert

def TailChunk000Sub001Block046Part017SupportExplicit : Finset ℕ :=
  ([10190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part017 : ℚ :=
  (648457040375 : ℚ) / 343738312468030464

def SurrogateDiagonalTailChunk000Sub001Block046Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10190
    = surrogateDiagTailX0RatChunk000Sub001Block046Part017

theorem surrogateDiagonalTailChunk000Sub001Block046Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part017] using hcert

def TailChunk000Sub001Block046Part018SupportExplicit : Finset ℕ :=
  ([10191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part018 : ℚ :=
  (744587859025 : ℚ) / 4608105504612599808

def SurrogateDiagonalTailChunk000Sub001Block046Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10191
    = surrogateDiagTailX0RatChunk000Sub001Block046Part018

theorem surrogateDiagonalTailChunk000Sub001Block046Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part018] using hcert

def TailChunk000Sub001Block046Part019SupportExplicit : Finset ℕ :=
  ([10193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block046Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10193
    = surrogateDiagTailX0RatChunk000Sub001Block046Part019

theorem surrogateDiagonalTailChunk000Sub001Block046Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part019] using hcert

def TailChunk000Sub001Block046Part020SupportExplicit : Finset ℕ :=
  ([10194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part020 : ℚ :=
  (36060875 : ℚ) / 11083820407488

def SurrogateDiagonalTailChunk000Sub001Block046Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10194
    = surrogateDiagTailX0RatChunk000Sub001Block046Part020

theorem surrogateDiagonalTailChunk000Sub001Block046Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part020] using hcert

def TailChunk000Sub001Block046Part021SupportExplicit : Finset ℕ :=
  ([10195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part021 : ℚ :=
  (520327177225 : ℚ) / 11042910259550865408

def SurrogateDiagonalTailChunk000Sub001Block046Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10195
    = surrogateDiagTailX0RatChunk000Sub001Block046Part021

theorem surrogateDiagonalTailChunk000Sub001Block046Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part021] using hcert

def TailChunk000Sub001Block046Part022SupportExplicit : Finset ℕ :=
  ([10198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part022 : ℚ :=
  (406246890625 : ℚ) / 422246629987519602

def SurrogateDiagonalTailChunk000Sub001Block046Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10198
    = surrogateDiagTailX0RatChunk000Sub001Block046Part022

theorem surrogateDiagonalTailChunk000Sub001Block046Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part022] using hcert

def TailChunk000Sub001Block046Part023SupportExplicit : Finset ℕ :=
  ([10199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part023 : ℚ :=
  (2479683701 : ℚ) / 58764928267526400

def SurrogateDiagonalTailChunk000Sub001Block046Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10199
    = surrogateDiagTailX0RatChunk000Sub001Block046Part023

theorem surrogateDiagonalTailChunk000Sub001Block046Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part023] using hcert

def TailChunk000Sub001Block046Part024SupportExplicit : Finset ℕ :=
  ([10202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block046Part024 : ℚ :=
  (26020201 : ℚ) / 27066216160800

def SurrogateDiagonalTailChunk000Sub001Block046Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10202
    = surrogateDiagTailX0RatChunk000Sub001Block046Part024

theorem surrogateDiagonalTailChunk000Sub001Block046Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block046Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block046Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block046Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block046Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block046Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block046Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block046HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block046Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block046Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block046Part000
    + surrogateDiagTailX0RatChunk000Sub001Block046Part001
    + surrogateDiagTailX0RatChunk000Sub001Block046Part002
    + surrogateDiagTailX0RatChunk000Sub001Block046Part003
    + surrogateDiagTailX0RatChunk000Sub001Block046Part004
    + surrogateDiagTailX0RatChunk000Sub001Block046Part005
    + surrogateDiagTailX0RatChunk000Sub001Block046Part006
    + surrogateDiagTailX0RatChunk000Sub001Block046Part007
    + surrogateDiagTailX0RatChunk000Sub001Block046Part008
    + surrogateDiagTailX0RatChunk000Sub001Block046Part009

def surrogateDiagonalTailChunk000Sub001Block046MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block046Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block046Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block046Part010
    + surrogateDiagTailX0RatChunk000Sub001Block046Part011
    + surrogateDiagTailX0RatChunk000Sub001Block046Part012
    + surrogateDiagTailX0RatChunk000Sub001Block046Part013
    + surrogateDiagTailX0RatChunk000Sub001Block046Part014
    + surrogateDiagTailX0RatChunk000Sub001Block046Part015
    + surrogateDiagTailX0RatChunk000Sub001Block046Part016
    + surrogateDiagTailX0RatChunk000Sub001Block046Part017
    + surrogateDiagTailX0RatChunk000Sub001Block046Part018
    + surrogateDiagTailX0RatChunk000Sub001Block046Part019

def surrogateDiagonalTailChunk000Sub001Block046TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block046Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block046Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block046Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block046Part020
    + surrogateDiagTailX0RatChunk000Sub001Block046Part021
    + surrogateDiagTailX0RatChunk000Sub001Block046Part022
    + surrogateDiagTailX0RatChunk000Sub001Block046Part023
    + surrogateDiagTailX0RatChunk000Sub001Block046Part024

def surrogateDiagonalTailChunk000Sub001Block046Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block046HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block046MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block046TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block046 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block046Part000
    + surrogateDiagTailX0RatChunk000Sub001Block046Part001
    + surrogateDiagTailX0RatChunk000Sub001Block046Part002
    + surrogateDiagTailX0RatChunk000Sub001Block046Part003
    + surrogateDiagTailX0RatChunk000Sub001Block046Part004
    + surrogateDiagTailX0RatChunk000Sub001Block046Part005
    + surrogateDiagTailX0RatChunk000Sub001Block046Part006
    + surrogateDiagTailX0RatChunk000Sub001Block046Part007
    + surrogateDiagTailX0RatChunk000Sub001Block046Part008
    + surrogateDiagTailX0RatChunk000Sub001Block046Part009
    + surrogateDiagTailX0RatChunk000Sub001Block046Part010
    + surrogateDiagTailX0RatChunk000Sub001Block046Part011
    + surrogateDiagTailX0RatChunk000Sub001Block046Part012
    + surrogateDiagTailX0RatChunk000Sub001Block046Part013
    + surrogateDiagTailX0RatChunk000Sub001Block046Part014
    + surrogateDiagTailX0RatChunk000Sub001Block046Part015
    + surrogateDiagTailX0RatChunk000Sub001Block046Part016
    + surrogateDiagTailX0RatChunk000Sub001Block046Part017
    + surrogateDiagTailX0RatChunk000Sub001Block046Part018
    + surrogateDiagTailX0RatChunk000Sub001Block046Part019
    + surrogateDiagTailX0RatChunk000Sub001Block046Part020
    + surrogateDiagTailX0RatChunk000Sub001Block046Part021
    + surrogateDiagTailX0RatChunk000Sub001Block046Part022
    + surrogateDiagTailX0RatChunk000Sub001Block046Part023
    + surrogateDiagTailX0RatChunk000Sub001Block046Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block046_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block046Head + surrogateDiagTailX0RatChunk000Sub001Block046Mid + surrogateDiagTailX0RatChunk000Sub001Block046Tail =
      surrogateDiagTailX0RatChunk000Sub001Block046 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block046Head surrogateDiagTailX0RatChunk000Sub001Block046Mid surrogateDiagTailX0RatChunk000Sub001Block046Tail surrogateDiagTailX0RatChunk000Sub001Block046
  ring

def SurrogateDiagonalTailChunk000Sub001Block046HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block046HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block046Head

def SurrogateDiagonalTailChunk000Sub001Block046MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block046MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block046Mid

def SurrogateDiagonalTailChunk000Sub001Block046TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block046TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block046Tail

theorem surrogateDiagonalTailChunk000Sub001Block046_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block046HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block046MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block046TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block046Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block046 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block046HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block046MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block046TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block046Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block046_eq_head_add_mid_add_tail

/-- Block 047 covers tail-support indices [6175,6200) and q from 10203 to 10243. -/

def TailChunk000Sub001Block047Part000SupportExplicit : Finset ℕ :=
  ([10203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part000 : ℚ :=
  (379897733225 : ℚ) / 2108078968676557824

def SurrogateDiagonalTailChunk000Sub001Block047Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10203
    = surrogateDiagTailX0RatChunk000Sub001Block047Part000

theorem surrogateDiagonalTailChunk000Sub001Block047Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part000] using hcert

def TailChunk000Sub001Block047Part001SupportExplicit : Finset ℕ :=
  ([10205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part001 : ℚ :=
  (76647048425 : ℚ) / 145578232425480192

def SurrogateDiagonalTailChunk000Sub001Block047Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10205
    = surrogateDiagTailX0RatChunk000Sub001Block047Part001

theorem surrogateDiagonalTailChunk000Sub001Block047Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part001] using hcert

def TailChunk000Sub001Block047Part002SupportExplicit : Finset ℕ :=
  ([10207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part002 : ℚ :=
  (1572674391925 : ℚ) / 6191453697738281472

def SurrogateDiagonalTailChunk000Sub001Block047Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10207
    = surrogateDiagTailX0RatChunk000Sub001Block047Part002

theorem surrogateDiagonalTailChunk000Sub001Block047Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part002] using hcert

def TailChunk000Sub001Block047Part003SupportExplicit : Finset ℕ :=
  ([10209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part003 : ℚ :=
  (6870333347 : ℚ) / 9261305535528960

def SurrogateDiagonalTailChunk000Sub001Block047Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10209
    = surrogateDiagTailX0RatChunk000Sub001Block047Part003

theorem surrogateDiagonalTailChunk000Sub001Block047Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part003] using hcert

def TailChunk000Sub001Block047Part004SupportExplicit : Finset ℕ :=
  ([10210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part004 : ℚ :=
  (5208040399 : ℚ) / 2771580534865920

def SurrogateDiagonalTailChunk000Sub001Block047Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10210
    = surrogateDiagTailX0RatChunk000Sub001Block047Part004

theorem surrogateDiagonalTailChunk000Sub001Block047Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part004] using hcert

def TailChunk000Sub001Block047Part005SupportExplicit : Finset ℕ :=
  ([10211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part005 : ℚ :=
  (2606613025 : ℚ) / 10869005751286962

def SurrogateDiagonalTailChunk000Sub001Block047Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10211
    = surrogateDiagTailX0RatChunk000Sub001Block047Part005

theorem surrogateDiagonalTailChunk000Sub001Block047Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part005] using hcert

def TailChunk000Sub001Block047Part006SupportExplicit : Finset ℕ :=
  ([10213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part006 : ℚ :=
  (288012146075 : ℚ) / 813559744478293056

def SurrogateDiagonalTailChunk000Sub001Block047Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10213
    = surrogateDiagTailX0RatChunk000Sub001Block047Part006

theorem surrogateDiagonalTailChunk000Sub001Block047Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part006] using hcert

def TailChunk000Sub001Block047Part007SupportExplicit : Finset ℕ :=
  ([10214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part007 : ℚ :=
  (407522640625 : ℚ) / 424903305273130962

def SurrogateDiagonalTailChunk000Sub001Block047Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10214
    = surrogateDiagTailX0RatChunk000Sub001Block047Part007

theorem surrogateDiagonalTailChunk000Sub001Block047Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part007] using hcert

def TailChunk000Sub001Block047Part008SupportExplicit : Finset ℕ :=
  ([10217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part008 : ℚ :=
  (237835254493 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk000Sub001Block047Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10217
    = surrogateDiagTailX0RatChunk000Sub001Block047Part008

theorem surrogateDiagonalTailChunk000Sub001Block047Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part008] using hcert

def TailChunk000Sub001Block047Part009SupportExplicit : Finset ℕ :=
  ([10218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part009 : ℚ :=
  (19841244803 : ℚ) / 4738874753433600

def SurrogateDiagonalTailChunk000Sub001Block047Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10218
    = surrogateDiagTailX0RatChunk000Sub001Block047Part009

theorem surrogateDiagonalTailChunk000Sub001Block047Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part009] using hcert

def TailChunk000Sub001Block047Part010SupportExplicit : Finset ℕ :=
  ([10219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part010 : ℚ :=
  (224061989089 : ℚ) / 741786209432371200

def SurrogateDiagonalTailChunk000Sub001Block047Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10219
    = surrogateDiagTailX0RatChunk000Sub001Block047Part010

theorem surrogateDiagonalTailChunk000Sub001Block047Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part010] using hcert

def TailChunk000Sub001Block047Part011SupportExplicit : Finset ℕ :=
  ([10221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part011 : ℚ :=
  (906616536025 : ℚ) / 1346063117780757792

def SurrogateDiagonalTailChunk000Sub001Block047Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10221
    = surrogateDiagTailX0RatChunk000Sub001Block047Part011

theorem surrogateDiagonalTailChunk000Sub001Block047Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part011] using hcert

def TailChunk000Sub001Block047Part012SupportExplicit : Finset ℕ :=
  ([10222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part012 : ℚ :=
  (385286666875 : ℚ) / 338529144785859072

def SurrogateDiagonalTailChunk000Sub001Block047Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10222
    = surrogateDiagTailX0RatChunk000Sub001Block047Part012

theorem surrogateDiagonalTailChunk000Sub001Block047Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part012] using hcert

def TailChunk000Sub001Block047Part013SupportExplicit : Finset ℕ :=
  ([10223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part013 : ℚ :=
  (1632964515625 : ℚ) / 6825121295579264082

def SurrogateDiagonalTailChunk000Sub001Block047Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10223
    = surrogateDiagTailX0RatChunk000Sub001Block047Part013

theorem surrogateDiagonalTailChunk000Sub001Block047Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part013] using hcert

def TailChunk000Sub001Block047Part014SupportExplicit : Finset ℕ :=
  ([10226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part014 : ℚ :=
  (408480765625 : ℚ) / 426904023676948992

def SurrogateDiagonalTailChunk000Sub001Block047Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10226
    = surrogateDiagTailX0RatChunk000Sub001Block047Part014

theorem surrogateDiagonalTailChunk000Sub001Block047Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part014] using hcert

def TailChunk000Sub001Block047Part015SupportExplicit : Finset ℕ :=
  ([10227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part015 : ℚ :=
  (1433998518725 : ℚ) / 1446328434628076544

def SurrogateDiagonalTailChunk000Sub001Block047Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10227
    = surrogateDiagTailX0RatChunk000Sub001Block047Part015

theorem surrogateDiagonalTailChunk000Sub001Block047Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part015] using hcert

def TailChunk000Sub001Block047Part016SupportExplicit : Finset ℕ :=
  ([10229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part016 : ℚ :=
  (1576183201825 : ℚ) / 6211337916820488192

def SurrogateDiagonalTailChunk000Sub001Block047Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10229
    = surrogateDiagTailX0RatChunk000Sub001Block047Part016

theorem surrogateDiagonalTailChunk000Sub001Block047Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part016] using hcert

def TailChunk000Sub001Block047Part017SupportExplicit : Finset ℕ :=
  ([10230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part017 : ℚ :=
  (30432257983 : ℚ) / 3318423552000000

def SurrogateDiagonalTailChunk000Sub001Block047Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10230
    = surrogateDiagTailX0RatChunk000Sub001Block047Part017

theorem surrogateDiagonalTailChunk000Sub001Block047Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part017] using hcert

def TailChunk000Sub001Block047Part018SupportExplicit : Finset ℕ :=
  ([10231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part018 : ℚ :=
  (639749113175 : ℚ) / 2198869816294213632

def SurrogateDiagonalTailChunk000Sub001Block047Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10231
    = surrogateDiagTailX0RatChunk000Sub001Block047Part018

theorem surrogateDiagonalTailChunk000Sub001Block047Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part018] using hcert

def TailChunk000Sub001Block047Part019SupportExplicit : Finset ℕ :=
  ([10234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part019 : ℚ :=
  (642474813425 : ℚ) / 330429609378054144

def SurrogateDiagonalTailChunk000Sub001Block047Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10234
    = surrogateDiagTailX0RatChunk000Sub001Block047Part019

theorem surrogateDiagonalTailChunk000Sub001Block047Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part019] using hcert

def TailChunk000Sub001Block047Part020SupportExplicit : Finset ℕ :=
  ([10235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part020 : ℚ :=
  (4109103222625 : ℚ) / 8992661292762267648

def SurrogateDiagonalTailChunk000Sub001Block047Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10235
    = surrogateDiagTailX0RatChunk000Sub001Block047Part020

theorem surrogateDiagonalTailChunk000Sub001Block047Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part020] using hcert

def TailChunk000Sub001Block047Part021SupportExplicit : Finset ℕ :=
  ([10237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part021 : ℚ :=
  (772691492975 : ℚ) / 2949440579731193856

def SurrogateDiagonalTailChunk000Sub001Block047Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10237
    = surrogateDiagTailX0RatChunk000Sub001Block047Part021

theorem surrogateDiagonalTailChunk000Sub001Block047Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part021] using hcert

def TailChunk000Sub001Block047Part022SupportExplicit : Finset ℕ :=
  ([10238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part022 : ℚ :=
  (409440015625 : ℚ) / 428911799280424722

def SurrogateDiagonalTailChunk000Sub001Block047Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10238
    = surrogateDiagTailX0RatChunk000Sub001Block047Part022

theorem surrogateDiagonalTailChunk000Sub001Block047Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part022] using hcert

def TailChunk000Sub001Block047Part023SupportExplicit : Finset ℕ :=
  ([10239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part023 : ℚ :=
  (2911060658725 : ℚ) / 5422292376088332288

def SurrogateDiagonalTailChunk000Sub001Block047Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10239
    = surrogateDiagTailX0RatChunk000Sub001Block047Part023

theorem surrogateDiagonalTailChunk000Sub001Block047Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part023] using hcert

def TailChunk000Sub001Block047Part024SupportExplicit : Finset ℕ :=
  ([10243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block047Part024 : ℚ :=
  (1639360140625 : ℚ) / 6878693419379967762

def SurrogateDiagonalTailChunk000Sub001Block047Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10243
    = surrogateDiagTailX0RatChunk000Sub001Block047Part024

theorem surrogateDiagonalTailChunk000Sub001Block047Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block047Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block047Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block047Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block047Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block047Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block047Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block047HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block047Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block047Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block047Part000
    + surrogateDiagTailX0RatChunk000Sub001Block047Part001
    + surrogateDiagTailX0RatChunk000Sub001Block047Part002
    + surrogateDiagTailX0RatChunk000Sub001Block047Part003
    + surrogateDiagTailX0RatChunk000Sub001Block047Part004
    + surrogateDiagTailX0RatChunk000Sub001Block047Part005
    + surrogateDiagTailX0RatChunk000Sub001Block047Part006
    + surrogateDiagTailX0RatChunk000Sub001Block047Part007
    + surrogateDiagTailX0RatChunk000Sub001Block047Part008
    + surrogateDiagTailX0RatChunk000Sub001Block047Part009

def surrogateDiagonalTailChunk000Sub001Block047MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block047Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block047Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block047Part010
    + surrogateDiagTailX0RatChunk000Sub001Block047Part011
    + surrogateDiagTailX0RatChunk000Sub001Block047Part012
    + surrogateDiagTailX0RatChunk000Sub001Block047Part013
    + surrogateDiagTailX0RatChunk000Sub001Block047Part014
    + surrogateDiagTailX0RatChunk000Sub001Block047Part015
    + surrogateDiagTailX0RatChunk000Sub001Block047Part016
    + surrogateDiagTailX0RatChunk000Sub001Block047Part017
    + surrogateDiagTailX0RatChunk000Sub001Block047Part018
    + surrogateDiagTailX0RatChunk000Sub001Block047Part019

def surrogateDiagonalTailChunk000Sub001Block047TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block047Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block047Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block047Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block047Part020
    + surrogateDiagTailX0RatChunk000Sub001Block047Part021
    + surrogateDiagTailX0RatChunk000Sub001Block047Part022
    + surrogateDiagTailX0RatChunk000Sub001Block047Part023
    + surrogateDiagTailX0RatChunk000Sub001Block047Part024

def surrogateDiagonalTailChunk000Sub001Block047Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block047HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block047MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block047TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block047 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block047Part000
    + surrogateDiagTailX0RatChunk000Sub001Block047Part001
    + surrogateDiagTailX0RatChunk000Sub001Block047Part002
    + surrogateDiagTailX0RatChunk000Sub001Block047Part003
    + surrogateDiagTailX0RatChunk000Sub001Block047Part004
    + surrogateDiagTailX0RatChunk000Sub001Block047Part005
    + surrogateDiagTailX0RatChunk000Sub001Block047Part006
    + surrogateDiagTailX0RatChunk000Sub001Block047Part007
    + surrogateDiagTailX0RatChunk000Sub001Block047Part008
    + surrogateDiagTailX0RatChunk000Sub001Block047Part009
    + surrogateDiagTailX0RatChunk000Sub001Block047Part010
    + surrogateDiagTailX0RatChunk000Sub001Block047Part011
    + surrogateDiagTailX0RatChunk000Sub001Block047Part012
    + surrogateDiagTailX0RatChunk000Sub001Block047Part013
    + surrogateDiagTailX0RatChunk000Sub001Block047Part014
    + surrogateDiagTailX0RatChunk000Sub001Block047Part015
    + surrogateDiagTailX0RatChunk000Sub001Block047Part016
    + surrogateDiagTailX0RatChunk000Sub001Block047Part017
    + surrogateDiagTailX0RatChunk000Sub001Block047Part018
    + surrogateDiagTailX0RatChunk000Sub001Block047Part019
    + surrogateDiagTailX0RatChunk000Sub001Block047Part020
    + surrogateDiagTailX0RatChunk000Sub001Block047Part021
    + surrogateDiagTailX0RatChunk000Sub001Block047Part022
    + surrogateDiagTailX0RatChunk000Sub001Block047Part023
    + surrogateDiagTailX0RatChunk000Sub001Block047Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block047_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block047Head + surrogateDiagTailX0RatChunk000Sub001Block047Mid + surrogateDiagTailX0RatChunk000Sub001Block047Tail =
      surrogateDiagTailX0RatChunk000Sub001Block047 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block047Head surrogateDiagTailX0RatChunk000Sub001Block047Mid surrogateDiagTailX0RatChunk000Sub001Block047Tail surrogateDiagTailX0RatChunk000Sub001Block047
  ring

def SurrogateDiagonalTailChunk000Sub001Block047HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block047HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block047Head

def SurrogateDiagonalTailChunk000Sub001Block047MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block047MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block047Mid

def SurrogateDiagonalTailChunk000Sub001Block047TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block047TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block047Tail

theorem surrogateDiagonalTailChunk000Sub001Block047_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block047HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block047MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block047TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block047Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block047 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block047HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block047MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block047TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block047Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block047_eq_head_add_mid_add_tail

/-- Block 048 covers tail-support indices [6200,6225) and q from 10245 to 10283. -/

def TailChunk000Sub001Block048Part000SupportExplicit : Finset ℕ :=
  ([10245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part000 : ℚ :=
  (1062170646575 : ℚ) / 1107884049628545024

def SurrogateDiagonalTailChunk000Sub001Block048Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10245
    = surrogateDiagTailX0RatChunk000Sub001Block048Part000

theorem surrogateDiagonalTailChunk000Sub001Block048Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part000] using hcert

def TailChunk000Sub001Block048Part001SupportExplicit : Finset ℕ :=
  ([10246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part001 : ℚ :=
  (1589876081875 : ℚ) / 1523186940694284288

def SurrogateDiagonalTailChunk000Sub001Block048Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10246
    = surrogateDiagTailX0RatChunk000Sub001Block048Part001

theorem surrogateDiagonalTailChunk000Sub001Block048Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part001] using hcert

def TailChunk000Sub001Block048Part002SupportExplicit : Finset ℕ :=
  ([10247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part002 : ℚ :=
  (1640640765625 : ℚ) / 6889445575858863282

def SurrogateDiagonalTailChunk000Sub001Block048Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10247
    = surrogateDiagTailX0RatChunk000Sub001Block048Part002

theorem surrogateDiagonalTailChunk000Sub001Block048Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part002] using hcert

def TailChunk000Sub001Block048Part003SupportExplicit : Finset ℕ :=
  ([10249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part003 : ℚ :=
  (782906937875 : ℚ) / 3046373881388568576

def SurrogateDiagonalTailChunk000Sub001Block048Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10249
    = surrogateDiagTailX0RatChunk000Sub001Block048Part003

theorem surrogateDiagonalTailChunk000Sub001Block048Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part003] using hcert

def TailChunk000Sub001Block048Part004SupportExplicit : Finset ℕ :=
  ([10253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part004 : ℚ :=
  (1642562640625 : ℚ) / 6905597438992894752

def SurrogateDiagonalTailChunk000Sub001Block048Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10253
    = surrogateDiagTailX0RatChunk000Sub001Block048Part004

theorem surrogateDiagonalTailChunk000Sub001Block048Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part004] using hcert

def TailChunk000Sub001Block048Part005SupportExplicit : Finset ℕ :=
  ([10254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part005 : ℚ :=
  (319125 : ℚ) / 99246988288

def SurrogateDiagonalTailChunk000Sub001Block048Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10254
    = surrogateDiagTailX0RatChunk000Sub001Block048Part005

theorem surrogateDiagonalTailChunk000Sub001Block048Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part005] using hcert

def TailChunk000Sub001Block048Part006SupportExplicit : Finset ℕ :=
  ([10255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part006 : ℚ :=
  (1847797236575 : ℚ) / 3015596536632705024

def SurrogateDiagonalTailChunk000Sub001Block048Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10255
    = surrogateDiagTailX0RatChunk000Sub001Block048Part006

theorem surrogateDiagonalTailChunk000Sub001Block048Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part006] using hcert

def TailChunk000Sub001Block048Part007SupportExplicit : Finset ℕ :=
  ([10257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part007 : ℚ :=
  (1316559680375 : ℚ) / 1954550947817078784

def SurrogateDiagonalTailChunk000Sub001Block048Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10257
    = surrogateDiagTailX0RatChunk000Sub001Block048Part007

theorem surrogateDiagonalTailChunk000Sub001Block048Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part007] using hcert

def TailChunk000Sub001Block048Part008SupportExplicit : Finset ℕ :=
  ([10258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part008 : ℚ :=
  (1562669730475 : ℚ) / 1422752901541411968

def SurrogateDiagonalTailChunk000Sub001Block048Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10258
    = surrogateDiagTailX0RatChunk000Sub001Block048Part008

theorem surrogateDiagonalTailChunk000Sub001Block048Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part008] using hcert

def TailChunk000Sub001Block048Part009SupportExplicit : Finset ℕ :=
  ([10259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part009 : ℚ :=
  (1644485640625 : ℚ) / 6921777685750215762

def SurrogateDiagonalTailChunk000Sub001Block048Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10259
    = surrogateDiagTailX0RatChunk000Sub001Block048Part009

theorem surrogateDiagonalTailChunk000Sub001Block048Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part009] using hcert

def TailChunk000Sub001Block048Part010SupportExplicit : Finset ℕ :=
  ([10261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part010 : ℚ :=
  (411974099 : ℚ) / 1588079552400000

def SurrogateDiagonalTailChunk000Sub001Block048Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10261
    = surrogateDiagTailX0RatChunk000Sub001Block048Part010

theorem surrogateDiagonalTailChunk000Sub001Block048Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part010] using hcert

def TailChunk000Sub001Block048Part011SupportExplicit : Finset ℕ :=
  ([10262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part011 : ℚ :=
  (1375189087975 : ℚ) / 930413888650856448

def SurrogateDiagonalTailChunk000Sub001Block048Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10262
    = surrogateDiagTailX0RatChunk000Sub001Block048Part011

theorem surrogateDiagonalTailChunk000Sub001Block048Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part011] using hcert

def TailChunk000Sub001Block048Part012SupportExplicit : Finset ℕ :=
  ([10263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part012 : ℚ :=
  (2588958451 : ℚ) / 3694822816800000

def SurrogateDiagonalTailChunk000Sub001Block048Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10263
    = surrogateDiagTailX0RatChunk000Sub001Block048Part012

theorem surrogateDiagonalTailChunk000Sub001Block048Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part012] using hcert

def TailChunk000Sub001Block048Part013SupportExplicit : Finset ℕ :=
  ([10265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part013 : ℚ :=
  (4475544411775 : ℚ) / 11349487476000718848

def SurrogateDiagonalTailChunk000Sub001Block048Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10265
    = surrogateDiagTailX0RatChunk000Sub001Block048Part013

theorem surrogateDiagonalTailChunk000Sub001Block048Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part013] using hcert

def TailChunk000Sub001Block048Part014SupportExplicit : Finset ℕ :=
  ([10266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part014 : ℚ :=
  (520615959125 : ℚ) / 139142866316181504

def SurrogateDiagonalTailChunk000Sub001Block048Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10266
    = surrogateDiagTailX0RatChunk000Sub001Block048Part014

theorem surrogateDiagonalTailChunk000Sub001Block048Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part014] using hcert

def TailChunk000Sub001Block048Part015SupportExplicit : Finset ℕ :=
  ([10267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part015 : ℚ :=
  (1647051390625 : ℚ) / 6943395557838491442

def SurrogateDiagonalTailChunk000Sub001Block048Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10267
    = surrogateDiagTailX0RatChunk000Sub001Block048Part015

theorem surrogateDiagonalTailChunk000Sub001Block048Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part015] using hcert

def TailChunk000Sub001Block048Part016SupportExplicit : Finset ℕ :=
  ([10270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part016 : ℚ :=
  (1200679166425 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk000Sub001Block048Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10270
    = surrogateDiagTailX0RatChunk000Sub001Block048Part016

theorem surrogateDiagonalTailChunk000Sub001Block048Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part016] using hcert

def TailChunk000Sub001Block048Part017SupportExplicit : Finset ℕ :=
  ([10271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part017 : ℚ :=
  (2637336025 : ℚ) / 11126757540936882

def SurrogateDiagonalTailChunk000Sub001Block048Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10271
    = surrogateDiagTailX0RatChunk000Sub001Block048Part017

theorem surrogateDiagonalTailChunk000Sub001Block048Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part017] using hcert

def TailChunk000Sub001Block048Part018SupportExplicit : Finset ℕ :=
  ([10273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part018 : ℚ :=
  (1648977015625 : ℚ) / 6959642162322604032

def SurrogateDiagonalTailChunk000Sub001Block048Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10273
    = surrogateDiagTailX0RatChunk000Sub001Block048Part018

theorem surrogateDiagonalTailChunk000Sub001Block048Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part018] using hcert

def TailChunk000Sub001Block048Part019SupportExplicit : Finset ℕ :=
  ([10274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part019 : ℚ :=
  (2992735427 : ℚ) / 2358307984083360

def SurrogateDiagonalTailChunk000Sub001Block048Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10274
    = surrogateDiagTailX0RatChunk000Sub001Block048Part019

theorem surrogateDiagonalTailChunk000Sub001Block048Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part019] using hcert

def TailChunk000Sub001Block048Part020SupportExplicit : Finset ℕ :=
  ([10277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part020 : ℚ :=
  (451875020225 : ℚ) / 1783215428457097152

def SurrogateDiagonalTailChunk000Sub001Block048Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10277
    = surrogateDiagTailX0RatChunk000Sub001Block048Part020

theorem surrogateDiagonalTailChunk000Sub001Block048Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part020] using hcert

def TailChunk000Sub001Block048Part021SupportExplicit : Finset ℕ :=
  ([10279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part021 : ℚ :=
  (242285839711 : ℚ) / 892795330017331200

def SurrogateDiagonalTailChunk000Sub001Block048Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10279
    = surrogateDiagTailX0RatChunk000Sub001Block048Part021

theorem surrogateDiagonalTailChunk000Sub001Block048Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part021] using hcert

def TailChunk000Sub001Block048Part022SupportExplicit : Finset ℕ :=
  ([10281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part022 : ℚ :=
  (3411919557325 : ℚ) / 4496601762896314368

def SurrogateDiagonalTailChunk000Sub001Block048Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10281
    = surrogateDiagTailX0RatChunk000Sub001Block048Part022

theorem surrogateDiagonalTailChunk000Sub001Block048Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part022] using hcert

def TailChunk000Sub001Block048Part023SupportExplicit : Finset ℕ :=
  ([10282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part023 : ℚ :=
  (534463333925 : ℚ) / 517611493068374016

def SurrogateDiagonalTailChunk000Sub001Block048Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10282
    = surrogateDiagTailX0RatChunk000Sub001Block048Part023

theorem surrogateDiagonalTailChunk000Sub001Block048Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part023] using hcert

def TailChunk000Sub001Block048Part024SupportExplicit : Finset ℕ :=
  ([10283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block048Part024 : ℚ :=
  (1120688651575 : ℚ) / 2643436875024433152

def SurrogateDiagonalTailChunk000Sub001Block048Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10283
    = surrogateDiagTailX0RatChunk000Sub001Block048Part024

theorem surrogateDiagonalTailChunk000Sub001Block048Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block048Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block048Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block048Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block048Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block048Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block048Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block048HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block048Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block048Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block048Part000
    + surrogateDiagTailX0RatChunk000Sub001Block048Part001
    + surrogateDiagTailX0RatChunk000Sub001Block048Part002
    + surrogateDiagTailX0RatChunk000Sub001Block048Part003
    + surrogateDiagTailX0RatChunk000Sub001Block048Part004
    + surrogateDiagTailX0RatChunk000Sub001Block048Part005
    + surrogateDiagTailX0RatChunk000Sub001Block048Part006
    + surrogateDiagTailX0RatChunk000Sub001Block048Part007
    + surrogateDiagTailX0RatChunk000Sub001Block048Part008
    + surrogateDiagTailX0RatChunk000Sub001Block048Part009

def surrogateDiagonalTailChunk000Sub001Block048MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block048Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block048Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block048Part010
    + surrogateDiagTailX0RatChunk000Sub001Block048Part011
    + surrogateDiagTailX0RatChunk000Sub001Block048Part012
    + surrogateDiagTailX0RatChunk000Sub001Block048Part013
    + surrogateDiagTailX0RatChunk000Sub001Block048Part014
    + surrogateDiagTailX0RatChunk000Sub001Block048Part015
    + surrogateDiagTailX0RatChunk000Sub001Block048Part016
    + surrogateDiagTailX0RatChunk000Sub001Block048Part017
    + surrogateDiagTailX0RatChunk000Sub001Block048Part018
    + surrogateDiagTailX0RatChunk000Sub001Block048Part019

def surrogateDiagonalTailChunk000Sub001Block048TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block048Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block048Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block048Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block048Part020
    + surrogateDiagTailX0RatChunk000Sub001Block048Part021
    + surrogateDiagTailX0RatChunk000Sub001Block048Part022
    + surrogateDiagTailX0RatChunk000Sub001Block048Part023
    + surrogateDiagTailX0RatChunk000Sub001Block048Part024

def surrogateDiagonalTailChunk000Sub001Block048Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block048HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block048MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block048TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block048 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block048Part000
    + surrogateDiagTailX0RatChunk000Sub001Block048Part001
    + surrogateDiagTailX0RatChunk000Sub001Block048Part002
    + surrogateDiagTailX0RatChunk000Sub001Block048Part003
    + surrogateDiagTailX0RatChunk000Sub001Block048Part004
    + surrogateDiagTailX0RatChunk000Sub001Block048Part005
    + surrogateDiagTailX0RatChunk000Sub001Block048Part006
    + surrogateDiagTailX0RatChunk000Sub001Block048Part007
    + surrogateDiagTailX0RatChunk000Sub001Block048Part008
    + surrogateDiagTailX0RatChunk000Sub001Block048Part009
    + surrogateDiagTailX0RatChunk000Sub001Block048Part010
    + surrogateDiagTailX0RatChunk000Sub001Block048Part011
    + surrogateDiagTailX0RatChunk000Sub001Block048Part012
    + surrogateDiagTailX0RatChunk000Sub001Block048Part013
    + surrogateDiagTailX0RatChunk000Sub001Block048Part014
    + surrogateDiagTailX0RatChunk000Sub001Block048Part015
    + surrogateDiagTailX0RatChunk000Sub001Block048Part016
    + surrogateDiagTailX0RatChunk000Sub001Block048Part017
    + surrogateDiagTailX0RatChunk000Sub001Block048Part018
    + surrogateDiagTailX0RatChunk000Sub001Block048Part019
    + surrogateDiagTailX0RatChunk000Sub001Block048Part020
    + surrogateDiagTailX0RatChunk000Sub001Block048Part021
    + surrogateDiagTailX0RatChunk000Sub001Block048Part022
    + surrogateDiagTailX0RatChunk000Sub001Block048Part023
    + surrogateDiagTailX0RatChunk000Sub001Block048Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block048_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block048Head + surrogateDiagTailX0RatChunk000Sub001Block048Mid + surrogateDiagTailX0RatChunk000Sub001Block048Tail =
      surrogateDiagTailX0RatChunk000Sub001Block048 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block048Head surrogateDiagTailX0RatChunk000Sub001Block048Mid surrogateDiagTailX0RatChunk000Sub001Block048Tail surrogateDiagTailX0RatChunk000Sub001Block048
  ring

def SurrogateDiagonalTailChunk000Sub001Block048HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block048HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block048Head

def SurrogateDiagonalTailChunk000Sub001Block048MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block048MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block048Mid

def SurrogateDiagonalTailChunk000Sub001Block048TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block048TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block048Tail

theorem surrogateDiagonalTailChunk000Sub001Block048_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block048HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block048MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block048TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block048Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block048 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block048HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block048MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block048TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block048Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block048_eq_head_add_mid_add_tail

/-- Block 049 covers tail-support indices [6225,6250) and q from 10286 to 10327. -/

def TailChunk000Sub001Block049Part000SupportExplicit : Finset ℕ :=
  ([10286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part000 : ℚ :=
  (1595697500425 : ℚ) / 1523186940694284288

def SurrogateDiagonalTailChunk000Sub001Block049Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10286
    = surrogateDiagTailX0RatChunk000Sub001Block049Part000

theorem surrogateDiagonalTailChunk000Sub001Block049Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part000] using hcert

def TailChunk000Sub001Block049Part001SupportExplicit : Finset ℕ :=
  ([10289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part001 : ℚ :=
  (1654117515625 : ℚ) / 7003105837716283392

def SurrogateDiagonalTailChunk000Sub001Block049Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10289
    = surrogateDiagTailX0RatChunk000Sub001Block049Part001

theorem surrogateDiagonalTailChunk000Sub001Block049Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part001] using hcert

def TailChunk000Sub001Block049Part002SupportExplicit : Finset ℕ :=
  ([10291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part002 : ℚ :=
  (25334407351 : ℚ) / 100020000000000000

def SurrogateDiagonalTailChunk000Sub001Block049Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10291
    = surrogateDiagTailX0RatChunk000Sub001Block049Part002

theorem surrogateDiagonalTailChunk000Sub001Block049Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part002] using hcert

def TailChunk000Sub001Block049Part003SupportExplicit : Finset ℕ :=
  ([10293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part003 : ℚ :=
  (1166032906825 : ℚ) / 1604674307891920896

def SurrogateDiagonalTailChunk000Sub001Block049Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10293
    = surrogateDiagTailX0RatChunk000Sub001Block049Part003

theorem surrogateDiagonalTailChunk000Sub001Block049Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part003] using hcert

def TailChunk000Sub001Block049Part004SupportExplicit : Finset ℕ :=
  ([10294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part004 : ℚ :=
  (413931390625 : ℚ) / 438375218194546482

def SurrogateDiagonalTailChunk000Sub001Block049Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10294
    = surrogateDiagTailX0RatChunk000Sub001Block049Part004

theorem surrogateDiagonalTailChunk000Sub001Block049Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part004] using hcert

def TailChunk000Sub001Block049Part005SupportExplicit : Finset ℕ :=
  ([10295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part005 : ℚ :=
  (44364342481 : ℚ) / 94469389683916800

def SurrogateDiagonalTailChunk000Sub001Block049Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10295
    = surrogateDiagTailX0RatChunk000Sub001Block049Part005

theorem surrogateDiagonalTailChunk000Sub001Block049Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part005] using hcert

def TailChunk000Sub001Block049Part006SupportExplicit : Finset ℕ :=
  ([10297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part006 : ℚ :=
  (11710835111 : ℚ) / 33627043495886400

def SurrogateDiagonalTailChunk000Sub001Block049Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10297
    = surrogateDiagTailX0RatChunk000Sub001Block049Part006

theorem surrogateDiagonalTailChunk000Sub001Block049Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part006] using hcert

def TailChunk000Sub001Block049Part007SupportExplicit : Finset ℕ :=
  ([10298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part007 : ℚ :=
  (31191854471 : ℚ) / 27899854063041600

def SurrogateDiagonalTailChunk000Sub001Block049Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10298
    = surrogateDiagTailX0RatChunk000Sub001Block049Part007

theorem surrogateDiagonalTailChunk000Sub001Block049Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part007] using hcert

def TailChunk000Sub001Block049Part008SupportExplicit : Finset ℕ :=
  ([10299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part008 : ℚ :=
  (1841016891425 : ℚ) / 2775274610600853504

def SurrogateDiagonalTailChunk000Sub001Block049Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10299
    = surrogateDiagTailX0RatChunk000Sub001Block049Part008

theorem surrogateDiagonalTailChunk000Sub001Block049Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part008] using hcert

def TailChunk000Sub001Block049Part009SupportExplicit : Finset ℕ :=
  ([10301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part009 : ℚ :=
  (106110601 : ℚ) / 450293564704800

def SurrogateDiagonalTailChunk000Sub001Block049Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10301
    = surrogateDiagTailX0RatChunk000Sub001Block049Part009

theorem surrogateDiagonalTailChunk000Sub001Block049Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part009] using hcert

def TailChunk000Sub001Block049Part010SupportExplicit : Finset ℕ :=
  ([10302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part010 : ℚ :=
  (8220796751 : ℚ) / 2097571430400000

def SurrogateDiagonalTailChunk000Sub001Block049Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10302
    = surrogateDiagTailX0RatChunk000Sub001Block049Part010

theorem surrogateDiagonalTailChunk000Sub001Block049Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part010] using hcert

def TailChunk000Sub001Block049Part011SupportExplicit : Finset ℕ :=
  ([10303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part011 : ℚ :=
  (1658622015625 : ℚ) / 7041303268113821202

def SurrogateDiagonalTailChunk000Sub001Block049Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10303
    = surrogateDiagTailX0RatChunk000Sub001Block049Part011

theorem surrogateDiagonalTailChunk000Sub001Block049Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part011] using hcert

def TailChunk000Sub001Block049Part012SupportExplicit : Finset ℕ :=
  ([10306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part012 : ℚ :=
  (414897015625 : ℚ) / 440423298268004352

def SurrogateDiagonalTailChunk000Sub001Block049Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10306
    = surrogateDiagTailX0RatChunk000Sub001Block049Part012

theorem surrogateDiagonalTailChunk000Sub001Block049Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part012] using hcert

def TailChunk000Sub001Block049Part013SupportExplicit : Finset ℕ :=
  ([10307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part013 : ℚ :=
  (9222937 : ℚ) / 639748091713536

def SurrogateDiagonalTailChunk000Sub001Block049Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10307
    = surrogateDiagTailX0RatChunk000Sub001Block049Part013

theorem surrogateDiagonalTailChunk000Sub001Block049Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part013] using hcert

def TailChunk000Sub001Block049Part014SupportExplicit : Finset ℕ :=
  ([10310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part014 : ℚ :=
  (5310560899 : ℚ) / 2881878814110720

def SurrogateDiagonalTailChunk000Sub001Block049Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10310
    = surrogateDiagTailX0RatChunk000Sub001Block049Part014

theorem surrogateDiagonalTailChunk000Sub001Block049Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part014] using hcert

def TailChunk000Sub001Block049Part015SupportExplicit : Finset ℕ :=
  ([10311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part015 : ℚ :=
  (201021563 : ℚ) / 738042106905600

def SurrogateDiagonalTailChunk000Sub001Block049Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10311
    = surrogateDiagTailX0RatChunk000Sub001Block049Part015

theorem surrogateDiagonalTailChunk000Sub001Block049Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part015] using hcert

def TailChunk000Sub001Block049Part016SupportExplicit : Finset ℕ :=
  ([10313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block049Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10313
    = surrogateDiagTailX0RatChunk000Sub001Block049Part016

theorem surrogateDiagonalTailChunk000Sub001Block049Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part016] using hcert

def TailChunk000Sub001Block049Part017SupportExplicit : Finset ℕ :=
  ([10315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part017 : ℚ :=
  (532624710025 : ℚ) / 11572347542922283008

def SurrogateDiagonalTailChunk000Sub001Block049Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10315
    = surrogateDiagTailX0RatChunk000Sub001Block049Part017

theorem surrogateDiagonalTailChunk000Sub001Block049Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part017] using hcert

def TailChunk000Sub001Block049Part018SupportExplicit : Finset ℕ :=
  ([10317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part018 : ℚ :=
  (31309570921 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub001Block049Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10317
    = surrogateDiagTailX0RatChunk000Sub001Block049Part018

theorem surrogateDiagonalTailChunk000Sub001Block049Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part018] using hcert

def TailChunk000Sub001Block049Part019SupportExplicit : Finset ℕ :=
  ([10318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part019 : ℚ :=
  (50658139501 : ℚ) / 24596176107571200

def SurrogateDiagonalTailChunk000Sub001Block049Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10318
    = surrogateDiagTailX0RatChunk000Sub001Block049Part019

theorem surrogateDiagonalTailChunk000Sub001Block049Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part019] using hcert

def TailChunk000Sub001Block049Part020SupportExplicit : Finset ℕ :=
  ([10319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part020 : ℚ :=
  (188359015525 : ℚ) / 22100255072573718528

def SurrogateDiagonalTailChunk000Sub001Block049Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10319
    = surrogateDiagTailX0RatChunk000Sub001Block049Part020

theorem surrogateDiagonalTailChunk000Sub001Block049Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part020] using hcert

def TailChunk000Sub001Block049Part021SupportExplicit : Finset ℕ :=
  ([10321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block049Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10321
    = surrogateDiagTailX0RatChunk000Sub001Block049Part021

theorem surrogateDiagonalTailChunk000Sub001Block049Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part021] using hcert

def TailChunk000Sub001Block049Part022SupportExplicit : Finset ℕ :=
  ([10322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part022 : ℚ :=
  (766503144875 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub001Block049Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10322
    = surrogateDiagTailX0RatChunk000Sub001Block049Part022

theorem surrogateDiagonalTailChunk000Sub001Block049Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part022] using hcert

def TailChunk000Sub001Block049Part023SupportExplicit : Finset ℕ :=
  ([10326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part023 : ℚ :=
  (4440099 : ℚ) / 1400340889600

def SurrogateDiagonalTailChunk000Sub001Block049Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10326
    = surrogateDiagTailX0RatChunk000Sub001Block049Part023

theorem surrogateDiagonalTailChunk000Sub001Block049Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part023] using hcert

def TailChunk000Sub001Block049Part024SupportExplicit : Finset ℕ :=
  ([10327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block049Part024 : ℚ :=
  (6023826825 : ℚ) / 983146859910397952

def SurrogateDiagonalTailChunk000Sub001Block049Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10327
    = surrogateDiagTailX0RatChunk000Sub001Block049Part024

theorem surrogateDiagonalTailChunk000Sub001Block049Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block049Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block049Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block049Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block049Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block049Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block049Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block049HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block049Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block049Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block049Part000
    + surrogateDiagTailX0RatChunk000Sub001Block049Part001
    + surrogateDiagTailX0RatChunk000Sub001Block049Part002
    + surrogateDiagTailX0RatChunk000Sub001Block049Part003
    + surrogateDiagTailX0RatChunk000Sub001Block049Part004
    + surrogateDiagTailX0RatChunk000Sub001Block049Part005
    + surrogateDiagTailX0RatChunk000Sub001Block049Part006
    + surrogateDiagTailX0RatChunk000Sub001Block049Part007
    + surrogateDiagTailX0RatChunk000Sub001Block049Part008
    + surrogateDiagTailX0RatChunk000Sub001Block049Part009

def surrogateDiagonalTailChunk000Sub001Block049MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block049Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block049Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block049Part010
    + surrogateDiagTailX0RatChunk000Sub001Block049Part011
    + surrogateDiagTailX0RatChunk000Sub001Block049Part012
    + surrogateDiagTailX0RatChunk000Sub001Block049Part013
    + surrogateDiagTailX0RatChunk000Sub001Block049Part014
    + surrogateDiagTailX0RatChunk000Sub001Block049Part015
    + surrogateDiagTailX0RatChunk000Sub001Block049Part016
    + surrogateDiagTailX0RatChunk000Sub001Block049Part017
    + surrogateDiagTailX0RatChunk000Sub001Block049Part018
    + surrogateDiagTailX0RatChunk000Sub001Block049Part019

def surrogateDiagonalTailChunk000Sub001Block049TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block049Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block049Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block049Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block049Part020
    + surrogateDiagTailX0RatChunk000Sub001Block049Part021
    + surrogateDiagTailX0RatChunk000Sub001Block049Part022
    + surrogateDiagTailX0RatChunk000Sub001Block049Part023
    + surrogateDiagTailX0RatChunk000Sub001Block049Part024

def surrogateDiagonalTailChunk000Sub001Block049Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block049HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block049MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block049TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block049 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block049Part000
    + surrogateDiagTailX0RatChunk000Sub001Block049Part001
    + surrogateDiagTailX0RatChunk000Sub001Block049Part002
    + surrogateDiagTailX0RatChunk000Sub001Block049Part003
    + surrogateDiagTailX0RatChunk000Sub001Block049Part004
    + surrogateDiagTailX0RatChunk000Sub001Block049Part005
    + surrogateDiagTailX0RatChunk000Sub001Block049Part006
    + surrogateDiagTailX0RatChunk000Sub001Block049Part007
    + surrogateDiagTailX0RatChunk000Sub001Block049Part008
    + surrogateDiagTailX0RatChunk000Sub001Block049Part009
    + surrogateDiagTailX0RatChunk000Sub001Block049Part010
    + surrogateDiagTailX0RatChunk000Sub001Block049Part011
    + surrogateDiagTailX0RatChunk000Sub001Block049Part012
    + surrogateDiagTailX0RatChunk000Sub001Block049Part013
    + surrogateDiagTailX0RatChunk000Sub001Block049Part014
    + surrogateDiagTailX0RatChunk000Sub001Block049Part015
    + surrogateDiagTailX0RatChunk000Sub001Block049Part016
    + surrogateDiagTailX0RatChunk000Sub001Block049Part017
    + surrogateDiagTailX0RatChunk000Sub001Block049Part018
    + surrogateDiagTailX0RatChunk000Sub001Block049Part019
    + surrogateDiagTailX0RatChunk000Sub001Block049Part020
    + surrogateDiagTailX0RatChunk000Sub001Block049Part021
    + surrogateDiagTailX0RatChunk000Sub001Block049Part022
    + surrogateDiagTailX0RatChunk000Sub001Block049Part023
    + surrogateDiagTailX0RatChunk000Sub001Block049Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block049_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block049Head + surrogateDiagTailX0RatChunk000Sub001Block049Mid + surrogateDiagTailX0RatChunk000Sub001Block049Tail =
      surrogateDiagTailX0RatChunk000Sub001Block049 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block049Head surrogateDiagTailX0RatChunk000Sub001Block049Mid surrogateDiagTailX0RatChunk000Sub001Block049Tail surrogateDiagTailX0RatChunk000Sub001Block049
  ring

def SurrogateDiagonalTailChunk000Sub001Block049HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block049HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block049Head

def SurrogateDiagonalTailChunk000Sub001Block049MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block049MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block049Mid

def SurrogateDiagonalTailChunk000Sub001Block049TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block049TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block049Tail

theorem surrogateDiagonalTailChunk000Sub001Block049_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block049HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block049MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block049TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block049Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block049 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block049HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block049MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block049TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block049Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block049_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
