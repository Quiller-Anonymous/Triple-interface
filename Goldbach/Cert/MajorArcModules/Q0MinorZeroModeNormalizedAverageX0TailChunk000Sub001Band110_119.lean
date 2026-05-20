import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [110,120). -/

/-- Block 110 covers tail-support indices [7750,7775) and q from 12805 to 12845. -/

def TailChunk000Sub001Block110Part000SupportExplicit : Finset ℕ :=
  ([12805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part000 : ℚ :=
  (313879185425 : ℚ) / 6529724214952329216

def SurrogateDiagonalTailChunk000Sub001Block110Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12805
    = surrogateDiagTailX0RatChunk000Sub001Block110Part000

theorem surrogateDiagonalTailChunk000Sub001Block110Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part000] using hcert

def TailChunk000Sub001Block110Part001SupportExplicit : Finset ℕ :=
  ([12806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part001 : ℚ :=
  (111164322175 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub001Block110Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12806
    = surrogateDiagTailX0RatChunk000Sub001Block110Part001

theorem surrogateDiagonalTailChunk000Sub001Block110Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part001] using hcert

def TailChunk000Sub001Block110Part002SupportExplicit : Finset ℕ :=
  ([12809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block110Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12809
    = surrogateDiagTailX0RatChunk000Sub001Block110Part002

theorem surrogateDiagonalTailChunk000Sub001Block110Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part002] using hcert

def TailChunk000Sub001Block110Part003SupportExplicit : Finset ℕ :=
  ([12810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part003 : ℚ :=
  (7751237483 : ℚ) / 2293694359142400

def SurrogateDiagonalTailChunk000Sub001Block110Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12810
    = surrogateDiagTailX0RatChunk000Sub001Block110Part003

theorem surrogateDiagonalTailChunk000Sub001Block110Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part003] using hcert

def TailChunk000Sub001Block110Part004SupportExplicit : Finset ℕ :=
  ([12811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part004 : ℚ :=
  (180474962725 : ℚ) / 55977918887825983488

def SurrogateDiagonalTailChunk000Sub001Block110Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12811
    = surrogateDiagTailX0RatChunk000Sub001Block110Part004

theorem surrogateDiagonalTailChunk000Sub001Block110Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part004] using hcert

def TailChunk000Sub001Block110Part005SupportExplicit : Finset ℕ :=
  ([12813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part005 : ℚ :=
  (93076027 : ℚ) / 1085731037186880

def SurrogateDiagonalTailChunk000Sub001Block110Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12813
    = surrogateDiagTailX0RatChunk000Sub001Block110Part005

theorem surrogateDiagonalTailChunk000Sub001Block110Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part005] using hcert

def TailChunk000Sub001Block110Part006SupportExplicit : Finset ℕ :=
  ([12814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part006 : ℚ :=
  (59435709475 : ℚ) / 3733110816584583168

def SurrogateDiagonalTailChunk000Sub001Block110Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12814
    = surrogateDiagTailX0RatChunk000Sub001Block110Part006

theorem surrogateDiagonalTailChunk000Sub001Block110Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part006] using hcert

def TailChunk000Sub001Block110Part007SupportExplicit : Finset ℕ :=
  ([12815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part007 : ℚ :=
  (254489241 : ℚ) / 4945241396215808

def SurrogateDiagonalTailChunk000Sub001Block110Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12815
    = surrogateDiagTailX0RatChunk000Sub001Block110Part007

theorem surrogateDiagonalTailChunk000Sub001Block110Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part007] using hcert

def TailChunk000Sub001Block110Part008SupportExplicit : Finset ℕ :=
  ([12817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part008 : ℚ :=
  (8408071127 : ℚ) / 726885850508481600

def SurrogateDiagonalTailChunk000Sub001Block110Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12817
    = surrogateDiagTailX0RatChunk000Sub001Block110Part008

theorem surrogateDiagonalTailChunk000Sub001Block110Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part008] using hcert

def TailChunk000Sub001Block110Part009SupportExplicit : Finset ℕ :=
  ([12818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part009 : ℚ :=
  (142397092925 : ℚ) / 1044320740750393344

def SurrogateDiagonalTailChunk000Sub001Block110Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12818
    = surrogateDiagTailX0RatChunk000Sub001Block110Part009

theorem surrogateDiagonalTailChunk000Sub001Block110Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part009] using hcert

def TailChunk000Sub001Block110Part010SupportExplicit : Finset ℕ :=
  ([12819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part010 : ℚ :=
  (285312270175 : ℚ) / 3331285283834560512

def SurrogateDiagonalTailChunk000Sub001Block110Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12819
    = surrogateDiagTailX0RatChunk000Sub001Block110Part010

theorem surrogateDiagonalTailChunk000Sub001Block110Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part010] using hcert

def TailChunk000Sub001Block110Part011SupportExplicit : Finset ℕ :=
  ([12821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part011 : ℚ :=
  (4109451025 : ℚ) / 27017113728037152

def SurrogateDiagonalTailChunk000Sub001Block110Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12821
    = surrogateDiagTailX0RatChunk000Sub001Block110Part011

theorem surrogateDiagonalTailChunk000Sub001Block110Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part011] using hcert

def TailChunk000Sub001Block110Part012SupportExplicit : Finset ℕ :=
  ([12822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part012 : ℚ :=
  (57052025 : ℚ) / 27755159666688

def SurrogateDiagonalTailChunk000Sub001Block110Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12822
    = surrogateDiagTailX0RatChunk000Sub001Block110Part012

theorem surrogateDiagonalTailChunk000Sub001Block110Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part012] using hcert

def TailChunk000Sub001Block110Part013SupportExplicit : Finset ℕ :=
  ([12823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part013 : ℚ :=
  (2569208265625 : ℚ) / 16896235641896506482

def SurrogateDiagonalTailChunk000Sub001Block110Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12823
    = surrogateDiagTailX0RatChunk000Sub001Block110Part013

theorem surrogateDiagonalTailChunk000Sub001Block110Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part013] using hcert

def TailChunk000Sub001Block110Part014SupportExplicit : Finset ℕ :=
  ([12827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part014 : ℚ :=
  (12490463009 : ℚ) / 78780557961000000

def SurrogateDiagonalTailChunk000Sub001Block110Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12827
    = surrogateDiagTailX0RatChunk000Sub001Block110Part014

theorem surrogateDiagonalTailChunk000Sub001Block110Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part014] using hcert

def TailChunk000Sub001Block110Part015SupportExplicit : Finset ℕ :=
  ([12829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part015 : ℚ :=
  (2571613140625 : ℚ) / 16927883932254649632

def SurrogateDiagonalTailChunk000Sub001Block110Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12829
    = surrogateDiagTailX0RatChunk000Sub001Block110Part015

theorem surrogateDiagonalTailChunk000Sub001Block110Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part015] using hcert

def TailChunk000Sub001Block110Part016SupportExplicit : Finset ℕ :=
  ([12830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part016 : ℚ :=
  (244163087675 : ℚ) / 216136909824297216

def SurrogateDiagonalTailChunk000Sub001Block110Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12830
    = surrogateDiagTailX0RatChunk000Sub001Block110Part016

theorem surrogateDiagonalTailChunk000Sub001Block110Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part016] using hcert

def TailChunk000Sub001Block110Part017SupportExplicit : Finset ℕ :=
  ([12831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part017 : ℚ :=
  (1920672057125 : ℚ) / 2407011461837881344

def SurrogateDiagonalTailChunk000Sub001Block110Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12831
    = surrogateDiagTailX0RatChunk000Sub001Block110Part017

theorem surrogateDiagonalTailChunk000Sub001Block110Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part017] using hcert

def TailChunk000Sub001Block110Part018SupportExplicit : Finset ℕ :=
  ([12833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part018 : ℚ :=
  (512461793 : ℚ) / 3159249835622400

def SurrogateDiagonalTailChunk000Sub001Block110Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12833
    = surrogateDiagTailX0RatChunk000Sub001Block110Part018

theorem surrogateDiagonalTailChunk000Sub001Block110Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part018] using hcert

def TailChunk000Sub001Block110Part019SupportExplicit : Finset ℕ :=
  ([12835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part019 : ℚ :=
  (251570180161 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk000Sub001Block110Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12835
    = surrogateDiagTailX0RatChunk000Sub001Block110Part019

theorem surrogateDiagonalTailChunk000Sub001Block110Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part019] using hcert

def TailChunk000Sub001Block110Part020SupportExplicit : Finset ℕ :=
  ([12837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part020 : ℚ :=
  (195984724951 : ℚ) / 362688458162995200

def SurrogateDiagonalTailChunk000Sub001Block110Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12837
    = surrogateDiagTailX0RatChunk000Sub001Block110Part020

theorem surrogateDiagonalTailChunk000Sub001Block110Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part020] using hcert

def TailChunk000Sub001Block110Part021SupportExplicit : Finset ℕ :=
  ([12839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part021 : ℚ :=
  (4907068855475 : ℚ) / 30096172086496257024

def SurrogateDiagonalTailChunk000Sub001Block110Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12839
    = surrogateDiagTailX0RatChunk000Sub001Block110Part021

theorem surrogateDiagonalTailChunk000Sub001Block110Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part021] using hcert

def TailChunk000Sub001Block110Part022SupportExplicit : Finset ℕ :=
  ([12841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part022 : ℚ :=
  (4122282025 : ℚ) / 27186102196572672

def SurrogateDiagonalTailChunk000Sub001Block110Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12841
    = surrogateDiagTailX0RatChunk000Sub001Block110Part022

theorem surrogateDiagonalTailChunk000Sub001Block110Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part022] using hcert

def TailChunk000Sub001Block110Part023SupportExplicit : Finset ℕ :=
  ([12842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part023 : ℚ :=
  (1030731025 : ℚ) / 1699131387285792

def SurrogateDiagonalTailChunk000Sub001Block110Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12842
    = surrogateDiagTailX0RatChunk000Sub001Block110Part023

theorem surrogateDiagonalTailChunk000Sub001Block110Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part023] using hcert

def TailChunk000Sub001Block110Part024SupportExplicit : Finset ℕ :=
  ([12845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block110Part024 : ℚ :=
  (5483339376025 : ℚ) / 14886622218413703168

def SurrogateDiagonalTailChunk000Sub001Block110Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12845
    = surrogateDiagTailX0RatChunk000Sub001Block110Part024

theorem surrogateDiagonalTailChunk000Sub001Block110Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block110Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block110Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block110Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block110Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block110Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block110Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block110HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block110Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block110Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block110Part000
    + surrogateDiagTailX0RatChunk000Sub001Block110Part001
    + surrogateDiagTailX0RatChunk000Sub001Block110Part002
    + surrogateDiagTailX0RatChunk000Sub001Block110Part003
    + surrogateDiagTailX0RatChunk000Sub001Block110Part004
    + surrogateDiagTailX0RatChunk000Sub001Block110Part005
    + surrogateDiagTailX0RatChunk000Sub001Block110Part006
    + surrogateDiagTailX0RatChunk000Sub001Block110Part007
    + surrogateDiagTailX0RatChunk000Sub001Block110Part008
    + surrogateDiagTailX0RatChunk000Sub001Block110Part009

def surrogateDiagonalTailChunk000Sub001Block110MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block110Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block110Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block110Part010
    + surrogateDiagTailX0RatChunk000Sub001Block110Part011
    + surrogateDiagTailX0RatChunk000Sub001Block110Part012
    + surrogateDiagTailX0RatChunk000Sub001Block110Part013
    + surrogateDiagTailX0RatChunk000Sub001Block110Part014
    + surrogateDiagTailX0RatChunk000Sub001Block110Part015
    + surrogateDiagTailX0RatChunk000Sub001Block110Part016
    + surrogateDiagTailX0RatChunk000Sub001Block110Part017
    + surrogateDiagTailX0RatChunk000Sub001Block110Part018
    + surrogateDiagTailX0RatChunk000Sub001Block110Part019

def surrogateDiagonalTailChunk000Sub001Block110TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block110Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block110Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block110Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block110Part020
    + surrogateDiagTailX0RatChunk000Sub001Block110Part021
    + surrogateDiagTailX0RatChunk000Sub001Block110Part022
    + surrogateDiagTailX0RatChunk000Sub001Block110Part023
    + surrogateDiagTailX0RatChunk000Sub001Block110Part024

def surrogateDiagonalTailChunk000Sub001Block110Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block110HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block110MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block110TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block110 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block110Part000
    + surrogateDiagTailX0RatChunk000Sub001Block110Part001
    + surrogateDiagTailX0RatChunk000Sub001Block110Part002
    + surrogateDiagTailX0RatChunk000Sub001Block110Part003
    + surrogateDiagTailX0RatChunk000Sub001Block110Part004
    + surrogateDiagTailX0RatChunk000Sub001Block110Part005
    + surrogateDiagTailX0RatChunk000Sub001Block110Part006
    + surrogateDiagTailX0RatChunk000Sub001Block110Part007
    + surrogateDiagTailX0RatChunk000Sub001Block110Part008
    + surrogateDiagTailX0RatChunk000Sub001Block110Part009
    + surrogateDiagTailX0RatChunk000Sub001Block110Part010
    + surrogateDiagTailX0RatChunk000Sub001Block110Part011
    + surrogateDiagTailX0RatChunk000Sub001Block110Part012
    + surrogateDiagTailX0RatChunk000Sub001Block110Part013
    + surrogateDiagTailX0RatChunk000Sub001Block110Part014
    + surrogateDiagTailX0RatChunk000Sub001Block110Part015
    + surrogateDiagTailX0RatChunk000Sub001Block110Part016
    + surrogateDiagTailX0RatChunk000Sub001Block110Part017
    + surrogateDiagTailX0RatChunk000Sub001Block110Part018
    + surrogateDiagTailX0RatChunk000Sub001Block110Part019
    + surrogateDiagTailX0RatChunk000Sub001Block110Part020
    + surrogateDiagTailX0RatChunk000Sub001Block110Part021
    + surrogateDiagTailX0RatChunk000Sub001Block110Part022
    + surrogateDiagTailX0RatChunk000Sub001Block110Part023
    + surrogateDiagTailX0RatChunk000Sub001Block110Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block110_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block110Head + surrogateDiagTailX0RatChunk000Sub001Block110Mid + surrogateDiagTailX0RatChunk000Sub001Block110Tail =
      surrogateDiagTailX0RatChunk000Sub001Block110 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block110Head surrogateDiagTailX0RatChunk000Sub001Block110Mid surrogateDiagTailX0RatChunk000Sub001Block110Tail surrogateDiagTailX0RatChunk000Sub001Block110
  ring

def SurrogateDiagonalTailChunk000Sub001Block110HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block110HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block110Head

def SurrogateDiagonalTailChunk000Sub001Block110MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block110MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block110Mid

def SurrogateDiagonalTailChunk000Sub001Block110TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block110TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block110Tail

theorem surrogateDiagonalTailChunk000Sub001Block110_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block110HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block110MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block110TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block110Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block110 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block110HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block110MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block110TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block110Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block110_eq_head_add_mid_add_tail

/-- Block 111 covers tail-support indices [7775,7800) and q from 12846 to 12885. -/

def TailChunk000Sub001Block111Part000SupportExplicit : Finset ℕ :=
  ([12846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part000 : ℚ :=
  (28639577279 : ℚ) / 16781544565785600

def SurrogateDiagonalTailChunk000Sub001Block111Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12846
    = surrogateDiagTailX0RatChunk000Sub001Block111Part000

theorem surrogateDiagonalTailChunk000Sub001Block111Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part000] using hcert

def TailChunk000Sub001Block111Part001SupportExplicit : Finset ℕ :=
  ([12847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part001 : ℚ :=
  (9704762009125 : ℚ) / 58660810829256050688

def SurrogateDiagonalTailChunk000Sub001Block111Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12847
    = surrogateDiagTailX0RatChunk000Sub001Block111Part001

theorem surrogateDiagonalTailChunk000Sub001Block111Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part001] using hcert

def TailChunk000Sub001Block111Part002SupportExplicit : Finset ℕ :=
  ([12849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part002 : ℚ :=
  (4584505571725 : ℚ) / 13450347145705876608

def SurrogateDiagonalTailChunk000Sub001Block111Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12849
    = surrogateDiagTailX0RatChunk000Sub001Block111Part002

theorem surrogateDiagonalTailChunk000Sub001Block111Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part002] using hcert

def TailChunk000Sub001Block111Part003SupportExplicit : Finset ℕ :=
  ([12851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part003 : ℚ :=
  (99998492401 : ℚ) / 630244463688000000

def SurrogateDiagonalTailChunk000Sub001Block111Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12851
    = surrogateDiagTailX0RatChunk000Sub001Block111Part003

theorem surrogateDiagonalTailChunk000Sub001Block111Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part003] using hcert

def TailChunk000Sub001Block111Part004SupportExplicit : Finset ℕ :=
  ([12853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part004 : ℚ :=
  (2581243890625 : ℚ) / 17054921903946085152

def SurrogateDiagonalTailChunk000Sub001Block111Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12853
    = surrogateDiagTailX0RatChunk000Sub001Block111Part004

theorem surrogateDiagonalTailChunk000Sub001Block111Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part004] using hcert

def TailChunk000Sub001Block111Part005SupportExplicit : Finset ℕ :=
  ([12854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part005 : ℚ :=
  (645411390625 : ℚ) / 1065932618996630322

def SurrogateDiagonalTailChunk000Sub001Block111Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12854
    = surrogateDiagTailX0RatChunk000Sub001Block111Part005

theorem surrogateDiagonalTailChunk000Sub001Block111Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part005] using hcert

def TailChunk000Sub001Block111Part006SupportExplicit : Finset ℕ :=
  ([12855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part006 : ℚ :=
  (1099849127175 : ℚ) / 1832992174438875136

def SurrogateDiagonalTailChunk000Sub001Block111Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12855
    = surrogateDiagTailX0RatChunk000Sub001Block111Part006

theorem surrogateDiagonalTailChunk000Sub001Block111Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part006] using hcert

def TailChunk000Sub001Block111Part007SupportExplicit : Finset ℕ :=
  ([12857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part007 : ℚ :=
  (8111517042325 : ℚ) / 37795468053938208768

def SurrogateDiagonalTailChunk000Sub001Block111Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12857
    = surrogateDiagTailX0RatChunk000Sub001Block111Part007

theorem surrogateDiagonalTailChunk000Sub001Block111Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part007] using hcert

def TailChunk000Sub001Block111Part008SupportExplicit : Finset ℕ :=
  ([12858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part008 : ℚ :=
  (358663885525 : ℚ) / 210554591406741792

def SurrogateDiagonalTailChunk000Sub001Block111Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12858
    = surrogateDiagTailX0RatChunk000Sub001Block111Part008

theorem surrogateDiagonalTailChunk000Sub001Block111Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part008] using hcert

def TailChunk000Sub001Block111Part009SupportExplicit : Finset ℕ :=
  ([12859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part009 : ℚ :=
  (26473679611 : ℚ) / 98429256340485120

def SurrogateDiagonalTailChunk000Sub001Block111Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12859
    = surrogateDiagTailX0RatChunk000Sub001Block111Part009

theorem surrogateDiagonalTailChunk000Sub001Block111Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part009] using hcert

def TailChunk000Sub001Block111Part010SupportExplicit : Finset ℕ :=
  ([12862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part010 : ℚ :=
  (2503602457675 : ℚ) / 3849761766864734208

def SurrogateDiagonalTailChunk000Sub001Block111Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12862
    = surrogateDiagTailX0RatChunk000Sub001Block111Part010

theorem surrogateDiagonalTailChunk000Sub001Block111Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part010] using hcert

def TailChunk000Sub001Block111Part011SupportExplicit : Finset ℕ :=
  ([12863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part011 : ℚ :=
  (4715895795725 : ℚ) / 27407767871145452544

def SurrogateDiagonalTailChunk000Sub001Block111Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12863
    = surrogateDiagTailX0RatChunk000Sub001Block111Part011

theorem surrogateDiagonalTailChunk000Sub001Block111Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part011] using hcert

def TailChunk000Sub001Block111Part012SupportExplicit : Finset ℕ :=
  ([12865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part012 : ℚ :=
  (10935451481 : ℚ) / 39071132728012800

def SurrogateDiagonalTailChunk000Sub001Block111Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12865
    = surrogateDiagTailX0RatChunk000Sub001Block111Part012

theorem surrogateDiagonalTailChunk000Sub001Block111Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part012] using hcert

def TailChunk000Sub001Block111Part013SupportExplicit : Finset ℕ :=
  ([12866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part013 : ℚ :=
  (124062429875 : ℚ) / 135379736307874944

def SurrogateDiagonalTailChunk000Sub001Block111Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12866
    = surrogateDiagTailX0RatChunk000Sub001Block111Part013

theorem surrogateDiagonalTailChunk000Sub001Block111Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part013] using hcert

def TailChunk000Sub001Block111Part014SupportExplicit : Finset ℕ :=
  ([12867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part014 : ℚ :=
  (4597360571125 : ℚ) / 13525893024042713088

def SurrogateDiagonalTailChunk000Sub001Block111Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12867
    = surrogateDiagTailX0RatChunk000Sub001Block111Part014

theorem surrogateDiagonalTailChunk000Sub001Block111Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part014] using hcert

def TailChunk000Sub001Block111Part015SupportExplicit : Finset ℕ :=
  ([12869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part015 : ℚ :=
  (4682519855075 : ℚ) / 26764798359622385664

def SurrogateDiagonalTailChunk000Sub001Block111Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12869
    = surrogateDiagTailX0RatChunk000Sub001Block111Part015

theorem surrogateDiagonalTailChunk000Sub001Block111Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part015] using hcert

def TailChunk000Sub001Block111Part016SupportExplicit : Finset ℕ :=
  ([12871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part016 : ℚ :=
  (2223480881 : ℚ) / 14005432526400000

def SurrogateDiagonalTailChunk000Sub001Block111Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12871
    = surrogateDiagTailX0RatChunk000Sub001Block111Part016

theorem surrogateDiagonalTailChunk000Sub001Block111Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part016] using hcert

def TailChunk000Sub001Block111Part017SupportExplicit : Finset ℕ :=
  ([12873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part017 : ℚ :=
  (919723510225 : ℚ) / 1818433988925530112

def SurrogateDiagonalTailChunk000Sub001Block111Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12873
    = surrogateDiagTailX0RatChunk000Sub001Block111Part017

theorem surrogateDiagonalTailChunk000Sub001Block111Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part017] using hcert

def TailChunk000Sub001Block111Part018SupportExplicit : Finset ℕ :=
  ([12874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part018 : ℚ :=
  (2493627709 : ℚ) / 3791099802746880

def SurrogateDiagonalTailChunk000Sub001Block111Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12874
    = surrogateDiagTailX0RatChunk000Sub001Block111Part018

theorem surrogateDiagonalTailChunk000Sub001Block111Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part018] using hcert

def TailChunk000Sub001Block111Part019SupportExplicit : Finset ℕ :=
  ([12877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part019 : ℚ :=
  (558533963075 : ℚ) / 3541545475086805056

def SurrogateDiagonalTailChunk000Sub001Block111Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12877
    = surrogateDiagTailX0RatChunk000Sub001Block111Part019

theorem surrogateDiagonalTailChunk000Sub001Block111Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part019] using hcert

def TailChunk000Sub001Block111Part020SupportExplicit : Finset ℕ :=
  ([12878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part020 : ℚ :=
  (834126067125 : ℚ) / 1276710894580105216

def SurrogateDiagonalTailChunk000Sub001Block111Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12878
    = surrogateDiagTailX0RatChunk000Sub001Block111Part020

theorem surrogateDiagonalTailChunk000Sub001Block111Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part020] using hcert

def TailChunk000Sub001Block111Part021SupportExplicit : Finset ℕ :=
  ([12881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part021 : ℚ :=
  (356085408529 : ℚ) / 1874261987442000000

def SurrogateDiagonalTailChunk000Sub001Block111Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12881
    = surrogateDiagTailX0RatChunk000Sub001Block111Part021

theorem surrogateDiagonalTailChunk000Sub001Block111Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part021] using hcert

def TailChunk000Sub001Block111Part022SupportExplicit : Finset ℕ :=
  ([12882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part022 : ℚ :=
  (1601409400825 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub001Block111Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12882
    = surrogateDiagTailX0RatChunk000Sub001Block111Part022

theorem surrogateDiagonalTailChunk000Sub001Block111Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part022] using hcert

def TailChunk000Sub001Block111Part023SupportExplicit : Finset ℕ :=
  ([12883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part023 : ℚ :=
  (181413966233 : ℚ) / 996145132356633600

def SurrogateDiagonalTailChunk000Sub001Block111Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12883
    = surrogateDiagTailX0RatChunk000Sub001Block111Part023

theorem surrogateDiagonalTailChunk000Sub001Block111Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part023] using hcert

def TailChunk000Sub001Block111Part024SupportExplicit : Finset ℕ :=
  ([12885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block111Part024 : ℚ :=
  (3130488349525 : ℚ) / 5550549221201707008

def SurrogateDiagonalTailChunk000Sub001Block111Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12885
    = surrogateDiagTailX0RatChunk000Sub001Block111Part024

theorem surrogateDiagonalTailChunk000Sub001Block111Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block111Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block111Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block111Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block111Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block111Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block111Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block111HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block111Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block111Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block111Part000
    + surrogateDiagTailX0RatChunk000Sub001Block111Part001
    + surrogateDiagTailX0RatChunk000Sub001Block111Part002
    + surrogateDiagTailX0RatChunk000Sub001Block111Part003
    + surrogateDiagTailX0RatChunk000Sub001Block111Part004
    + surrogateDiagTailX0RatChunk000Sub001Block111Part005
    + surrogateDiagTailX0RatChunk000Sub001Block111Part006
    + surrogateDiagTailX0RatChunk000Sub001Block111Part007
    + surrogateDiagTailX0RatChunk000Sub001Block111Part008
    + surrogateDiagTailX0RatChunk000Sub001Block111Part009

def surrogateDiagonalTailChunk000Sub001Block111MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block111Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block111Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block111Part010
    + surrogateDiagTailX0RatChunk000Sub001Block111Part011
    + surrogateDiagTailX0RatChunk000Sub001Block111Part012
    + surrogateDiagTailX0RatChunk000Sub001Block111Part013
    + surrogateDiagTailX0RatChunk000Sub001Block111Part014
    + surrogateDiagTailX0RatChunk000Sub001Block111Part015
    + surrogateDiagTailX0RatChunk000Sub001Block111Part016
    + surrogateDiagTailX0RatChunk000Sub001Block111Part017
    + surrogateDiagTailX0RatChunk000Sub001Block111Part018
    + surrogateDiagTailX0RatChunk000Sub001Block111Part019

def surrogateDiagonalTailChunk000Sub001Block111TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block111Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block111Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block111Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block111Part020
    + surrogateDiagTailX0RatChunk000Sub001Block111Part021
    + surrogateDiagTailX0RatChunk000Sub001Block111Part022
    + surrogateDiagTailX0RatChunk000Sub001Block111Part023
    + surrogateDiagTailX0RatChunk000Sub001Block111Part024

def surrogateDiagonalTailChunk000Sub001Block111Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block111HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block111MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block111TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block111 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block111Part000
    + surrogateDiagTailX0RatChunk000Sub001Block111Part001
    + surrogateDiagTailX0RatChunk000Sub001Block111Part002
    + surrogateDiagTailX0RatChunk000Sub001Block111Part003
    + surrogateDiagTailX0RatChunk000Sub001Block111Part004
    + surrogateDiagTailX0RatChunk000Sub001Block111Part005
    + surrogateDiagTailX0RatChunk000Sub001Block111Part006
    + surrogateDiagTailX0RatChunk000Sub001Block111Part007
    + surrogateDiagTailX0RatChunk000Sub001Block111Part008
    + surrogateDiagTailX0RatChunk000Sub001Block111Part009
    + surrogateDiagTailX0RatChunk000Sub001Block111Part010
    + surrogateDiagTailX0RatChunk000Sub001Block111Part011
    + surrogateDiagTailX0RatChunk000Sub001Block111Part012
    + surrogateDiagTailX0RatChunk000Sub001Block111Part013
    + surrogateDiagTailX0RatChunk000Sub001Block111Part014
    + surrogateDiagTailX0RatChunk000Sub001Block111Part015
    + surrogateDiagTailX0RatChunk000Sub001Block111Part016
    + surrogateDiagTailX0RatChunk000Sub001Block111Part017
    + surrogateDiagTailX0RatChunk000Sub001Block111Part018
    + surrogateDiagTailX0RatChunk000Sub001Block111Part019
    + surrogateDiagTailX0RatChunk000Sub001Block111Part020
    + surrogateDiagTailX0RatChunk000Sub001Block111Part021
    + surrogateDiagTailX0RatChunk000Sub001Block111Part022
    + surrogateDiagTailX0RatChunk000Sub001Block111Part023
    + surrogateDiagTailX0RatChunk000Sub001Block111Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block111_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block111Head + surrogateDiagTailX0RatChunk000Sub001Block111Mid + surrogateDiagTailX0RatChunk000Sub001Block111Tail =
      surrogateDiagTailX0RatChunk000Sub001Block111 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block111Head surrogateDiagTailX0RatChunk000Sub001Block111Mid surrogateDiagTailX0RatChunk000Sub001Block111Tail surrogateDiagTailX0RatChunk000Sub001Block111
  ring

def SurrogateDiagonalTailChunk000Sub001Block111HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block111HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block111Head

def SurrogateDiagonalTailChunk000Sub001Block111MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block111MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block111Mid

def SurrogateDiagonalTailChunk000Sub001Block111TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block111TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block111Tail

theorem surrogateDiagonalTailChunk000Sub001Block111_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block111HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block111MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block111TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block111Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block111 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block111HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block111MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block111TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block111Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block111_eq_head_add_mid_add_tail

/-- Block 112 covers tail-support indices [7800,7825) and q from 12886 to 12923. -/

def TailChunk000Sub001Block112Part000SupportExplicit : Finset ℕ :=
  ([12886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part000 : ℚ :=
  (2398739253175 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub001Block112Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12886
    = surrogateDiagTailX0RatChunk000Sub001Block112Part000

theorem surrogateDiagonalTailChunk000Sub001Block112Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part000] using hcert

def TailChunk000Sub001Block112Part001SupportExplicit : Finset ℕ :=
  ([12889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part001 : ℚ :=
  (2595723765625 : ℚ) / 17246817872024596992

def SurrogateDiagonalTailChunk000Sub001Block112Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12889
    = surrogateDiagTailX0RatChunk000Sub001Block112Part001

theorem surrogateDiagonalTailChunk000Sub001Block112Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part001] using hcert

def TailChunk000Sub001Block112Part002SupportExplicit : Finset ℕ :=
  ([12890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part002 : ℚ :=
  (985809710675 : ℚ) / 880846596536008704

def SurrogateDiagonalTailChunk000Sub001Block112Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12890
    = surrogateDiagTailX0RatChunk000Sub001Block112Part002

theorem surrogateDiagonalTailChunk000Sub001Block112Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part002] using hcert

def TailChunk000Sub001Block112Part003SupportExplicit : Finset ℕ :=
  ([12891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part003 : ℚ :=
  (4614528570325 : ℚ) / 13627115355673755648

def SurrogateDiagonalTailChunk000Sub001Block112Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12891
    = surrogateDiagTailX0RatChunk000Sub001Block112Part003

theorem surrogateDiagonalTailChunk000Sub001Block112Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part003] using hcert

def TailChunk000Sub001Block112Part004SupportExplicit : Finset ℕ :=
  ([12893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part004 : ℚ :=
  (2597335140625 : ℚ) / 17268239161631438112

def SurrogateDiagonalTailChunk000Sub001Block112Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12893
    = surrogateDiagTailX0RatChunk000Sub001Block112Part004

theorem surrogateDiagonalTailChunk000Sub001Block112Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part004] using hcert

def TailChunk000Sub001Block112Part005SupportExplicit : Finset ℕ :=
  ([12894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part005 : ℚ :=
  (306767995225 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub001Block112Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12894
    = surrogateDiagTailX0RatChunk000Sub001Block112Part005

theorem surrogateDiagonalTailChunk000Sub001Block112Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part005] using hcert

def TailChunk000Sub001Block112Part006SupportExplicit : Finset ℕ :=
  ([12895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part006 : ℚ :=
  (7063379239225 : ℚ) / 28274730637800327168

def SurrogateDiagonalTailChunk000Sub001Block112Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12895
    = surrogateDiagTailX0RatChunk000Sub001Block112Part006

theorem surrogateDiagonalTailChunk000Sub001Block112Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part006] using hcert

def TailChunk000Sub001Block112Part007SupportExplicit : Finset ℕ :=
  ([12898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part007 : ℚ :=
  (649837515625 : ℚ) / 1080605024979197952

def SurrogateDiagonalTailChunk000Sub001Block112Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12898
    = surrogateDiagTailX0RatChunk000Sub001Block112Part007

theorem surrogateDiagonalTailChunk000Sub001Block112Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part007] using hcert

def TailChunk000Sub001Block112Part008SupportExplicit : Finset ℕ :=
  ([12899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part008 : ℚ :=
  (2599753140625 : ℚ) / 17300408503214688402

def SurrogateDiagonalTailChunk000Sub001Block112Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12899
    = surrogateDiagTailX0RatChunk000Sub001Block112Part008

theorem surrogateDiagonalTailChunk000Sub001Block112Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part008] using hcert

def TailChunk000Sub001Block112Part009SupportExplicit : Finset ℕ :=
  ([12901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part009 : ℚ :=
  (7274143491175 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk000Sub001Block112Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12901
    = surrogateDiagTailX0RatChunk000Sub001Block112Part009

theorem surrogateDiagonalTailChunk000Sub001Block112Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part009] using hcert

def TailChunk000Sub001Block112Part010SupportExplicit : Finset ℕ :=
  ([12902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part010 : ℚ :=
  (41615401 : ℚ) / 69244566394050

def SurrogateDiagonalTailChunk000Sub001Block112Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12902
    = surrogateDiagTailX0RatChunk000Sub001Block112Part010

theorem surrogateDiagonalTailChunk000Sub001Block112Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part010] using hcert

def TailChunk000Sub001Block112Part011SupportExplicit : Finset ℕ :=
  ([12903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part011 : ℚ :=
  (139078383739 : ℚ) / 245684346499891200

def SurrogateDiagonalTailChunk000Sub001Block112Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12903
    = surrogateDiagTailX0RatChunk000Sub001Block112Part011

theorem surrogateDiagonalTailChunk000Sub001Block112Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part011] using hcert

def TailChunk000Sub001Block112Part012SupportExplicit : Finset ℕ :=
  ([12905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part012 : ℚ :=
  (274344696225 : ℚ) / 983146859910397952

def SurrogateDiagonalTailChunk000Sub001Block112Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12905
    = surrogateDiagTailX0RatChunk000Sub001Block112Part012

theorem surrogateDiagonalTailChunk000Sub001Block112Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part012] using hcert

def TailChunk000Sub001Block112Part013SupportExplicit : Finset ℕ :=
  ([12907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part013 : ℚ :=
  (2602978890625 : ℚ) / 17343370850390773362

def SurrogateDiagonalTailChunk000Sub001Block112Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12907
    = surrogateDiagTailX0RatChunk000Sub001Block112Part013

theorem surrogateDiagonalTailChunk000Sub001Block112Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part013] using hcert

def TailChunk000Sub001Block112Part014SupportExplicit : Finset ℕ :=
  ([12909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part014 : ℚ :=
  (18243179167 : ℚ) / 43726535302348800

def SurrogateDiagonalTailChunk000Sub001Block112Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12909
    = surrogateDiagTailX0RatChunk000Sub001Block112Part014

theorem surrogateDiagonalTailChunk000Sub001Block112Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part014] using hcert

def TailChunk000Sub001Block112Part015SupportExplicit : Finset ℕ :=
  ([12910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part015 : ℚ :=
  (1648119443 : ℚ) / 1477217416406400

def SurrogateDiagonalTailChunk000Sub001Block112Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12910
    = surrogateDiagTailX0RatChunk000Sub001Block112Part015

theorem surrogateDiagonalTailChunk000Sub001Block112Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part015] using hcert

def TailChunk000Sub001Block112Part016SupportExplicit : Finset ℕ :=
  ([12911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part016 : ℚ :=
  (4167348025 : ℚ) / 27783811208721522

def SurrogateDiagonalTailChunk000Sub001Block112Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12911
    = surrogateDiagTailX0RatChunk000Sub001Block112Part016

theorem surrogateDiagonalTailChunk000Sub001Block112Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part016] using hcert

def TailChunk000Sub001Block112Part017SupportExplicit : Finset ℕ :=
  ([12913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part017 : ℚ :=
  (4960077747275 : ℚ) / 30798094134917873664

def SurrogateDiagonalTailChunk000Sub001Block112Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12913
    = surrogateDiagTailX0RatChunk000Sub001Block112Part017

theorem surrogateDiagonalTailChunk000Sub001Block112Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part017] using hcert

def TailChunk000Sub001Block112Part018SupportExplicit : Finset ℕ :=
  ([12914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part018 : ℚ :=
  (30953216301 : ℚ) / 39314798992854400

def SurrogateDiagonalTailChunk000Sub001Block112Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12914
    = surrogateDiagTailX0RatChunk000Sub001Block112Part018

theorem surrogateDiagonalTailChunk000Sub001Block112Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part018] using hcert

def TailChunk000Sub001Block112Part019SupportExplicit : Finset ℕ :=
  ([12917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part019 : ℚ :=
  (2607013890625 : ℚ) / 17397186249738607392

def SurrogateDiagonalTailChunk000Sub001Block112Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12917
    = surrogateDiagTailX0RatChunk000Sub001Block112Part019

theorem surrogateDiagonalTailChunk000Sub001Block112Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part019] using hcert

def TailChunk000Sub001Block112Part020SupportExplicit : Finset ℕ :=
  ([12918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part020 : ℚ :=
  (724038219425 : ℚ) / 429028273673355264

def SurrogateDiagonalTailChunk000Sub001Block112Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12918
    = surrogateDiagTailX0RatChunk000Sub001Block112Part020

theorem surrogateDiagonalTailChunk000Sub001Block112Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part020] using hcert

def TailChunk000Sub001Block112Part021SupportExplicit : Finset ℕ :=
  ([12919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part021 : ℚ :=
  (2607821265625 : ℚ) / 17407964340486369522

def SurrogateDiagonalTailChunk000Sub001Block112Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12919
    = surrogateDiagTailX0RatChunk000Sub001Block112Part021

theorem surrogateDiagonalTailChunk000Sub001Block112Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part021] using hcert

def TailChunk000Sub001Block112Part022SupportExplicit : Finset ℕ :=
  ([12921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part022 : ℚ :=
  (277359141025 : ℚ) / 760446768763404288

def SurrogateDiagonalTailChunk000Sub001Block112Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12921
    = surrogateDiagTailX0RatChunk000Sub001Block112Part022

theorem surrogateDiagonalTailChunk000Sub001Block112Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part022] using hcert

def TailChunk000Sub001Block112Part023SupportExplicit : Finset ℕ :=
  ([12922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part023 : ℚ :=
  (77866992169 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk000Sub001Block112Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12922
    = surrogateDiagTailX0RatChunk000Sub001Block112Part023

theorem surrogateDiagonalTailChunk000Sub001Block112Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part023] using hcert

def TailChunk000Sub001Block112Part024SupportExplicit : Finset ℕ :=
  ([12923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block112Part024 : ℚ :=
  (2609436390625 : ℚ) / 17429535545261448882

def SurrogateDiagonalTailChunk000Sub001Block112Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12923
    = surrogateDiagTailX0RatChunk000Sub001Block112Part024

theorem surrogateDiagonalTailChunk000Sub001Block112Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block112Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block112Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block112Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block112Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block112Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block112Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block112HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block112Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block112Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block112Part000
    + surrogateDiagTailX0RatChunk000Sub001Block112Part001
    + surrogateDiagTailX0RatChunk000Sub001Block112Part002
    + surrogateDiagTailX0RatChunk000Sub001Block112Part003
    + surrogateDiagTailX0RatChunk000Sub001Block112Part004
    + surrogateDiagTailX0RatChunk000Sub001Block112Part005
    + surrogateDiagTailX0RatChunk000Sub001Block112Part006
    + surrogateDiagTailX0RatChunk000Sub001Block112Part007
    + surrogateDiagTailX0RatChunk000Sub001Block112Part008
    + surrogateDiagTailX0RatChunk000Sub001Block112Part009

def surrogateDiagonalTailChunk000Sub001Block112MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block112Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block112Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block112Part010
    + surrogateDiagTailX0RatChunk000Sub001Block112Part011
    + surrogateDiagTailX0RatChunk000Sub001Block112Part012
    + surrogateDiagTailX0RatChunk000Sub001Block112Part013
    + surrogateDiagTailX0RatChunk000Sub001Block112Part014
    + surrogateDiagTailX0RatChunk000Sub001Block112Part015
    + surrogateDiagTailX0RatChunk000Sub001Block112Part016
    + surrogateDiagTailX0RatChunk000Sub001Block112Part017
    + surrogateDiagTailX0RatChunk000Sub001Block112Part018
    + surrogateDiagTailX0RatChunk000Sub001Block112Part019

def surrogateDiagonalTailChunk000Sub001Block112TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block112Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block112Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block112Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block112Part020
    + surrogateDiagTailX0RatChunk000Sub001Block112Part021
    + surrogateDiagTailX0RatChunk000Sub001Block112Part022
    + surrogateDiagTailX0RatChunk000Sub001Block112Part023
    + surrogateDiagTailX0RatChunk000Sub001Block112Part024

def surrogateDiagonalTailChunk000Sub001Block112Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block112HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block112MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block112TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block112 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block112Part000
    + surrogateDiagTailX0RatChunk000Sub001Block112Part001
    + surrogateDiagTailX0RatChunk000Sub001Block112Part002
    + surrogateDiagTailX0RatChunk000Sub001Block112Part003
    + surrogateDiagTailX0RatChunk000Sub001Block112Part004
    + surrogateDiagTailX0RatChunk000Sub001Block112Part005
    + surrogateDiagTailX0RatChunk000Sub001Block112Part006
    + surrogateDiagTailX0RatChunk000Sub001Block112Part007
    + surrogateDiagTailX0RatChunk000Sub001Block112Part008
    + surrogateDiagTailX0RatChunk000Sub001Block112Part009
    + surrogateDiagTailX0RatChunk000Sub001Block112Part010
    + surrogateDiagTailX0RatChunk000Sub001Block112Part011
    + surrogateDiagTailX0RatChunk000Sub001Block112Part012
    + surrogateDiagTailX0RatChunk000Sub001Block112Part013
    + surrogateDiagTailX0RatChunk000Sub001Block112Part014
    + surrogateDiagTailX0RatChunk000Sub001Block112Part015
    + surrogateDiagTailX0RatChunk000Sub001Block112Part016
    + surrogateDiagTailX0RatChunk000Sub001Block112Part017
    + surrogateDiagTailX0RatChunk000Sub001Block112Part018
    + surrogateDiagTailX0RatChunk000Sub001Block112Part019
    + surrogateDiagTailX0RatChunk000Sub001Block112Part020
    + surrogateDiagTailX0RatChunk000Sub001Block112Part021
    + surrogateDiagTailX0RatChunk000Sub001Block112Part022
    + surrogateDiagTailX0RatChunk000Sub001Block112Part023
    + surrogateDiagTailX0RatChunk000Sub001Block112Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block112_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block112Head + surrogateDiagTailX0RatChunk000Sub001Block112Mid + surrogateDiagTailX0RatChunk000Sub001Block112Tail =
      surrogateDiagTailX0RatChunk000Sub001Block112 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block112Head surrogateDiagTailX0RatChunk000Sub001Block112Mid surrogateDiagTailX0RatChunk000Sub001Block112Tail surrogateDiagTailX0RatChunk000Sub001Block112
  ring

def SurrogateDiagonalTailChunk000Sub001Block112HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block112HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block112Head

def SurrogateDiagonalTailChunk000Sub001Block112MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block112MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block112Mid

def SurrogateDiagonalTailChunk000Sub001Block112TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block112TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block112Tail

theorem surrogateDiagonalTailChunk000Sub001Block112_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block112HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block112MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block112TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block112Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block112 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block112HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block112MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block112TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block112Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block112_eq_head_add_mid_add_tail

/-- Block 113 covers tail-support indices [7825,7850) and q from 12926 to 12966. -/

def TailChunk000Sub001Block113Part000SupportExplicit : Finset ℕ :=
  ([12926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part000 : ℚ :=
  (98487970243 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub001Block113Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12926
    = surrogateDiagTailX0RatChunk000Sub001Block113Part000

theorem surrogateDiagonalTailChunk000Sub001Block113Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part000] using hcert

def TailChunk000Sub001Block113Part001SupportExplicit : Finset ℕ :=
  ([12927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part001 : ℚ :=
  (7624933229 : ℚ) / 20439975049574400

def SurrogateDiagonalTailChunk000Sub001Block113Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12927
    = surrogateDiagTailX0RatChunk000Sub001Block113Part001

theorem surrogateDiagonalTailChunk000Sub001Block113Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part001] using hcert

def TailChunk000Sub001Block113Part002SupportExplicit : Finset ℕ :=
  ([12929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part002 : ℚ :=
  (506008360375 : ℚ) / 2352007295570474568

def SurrogateDiagonalTailChunk000Sub001Block113Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12929
    = surrogateDiagTailX0RatChunk000Sub001Block113Part002

theorem surrogateDiagonalTailChunk000Sub001Block113Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part002] using hcert

def TailChunk000Sub001Block113Part003SupportExplicit : Finset ℕ :=
  ([12930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part003 : ℚ :=
  (7567972779 : ℚ) / 2334368262963200

def SurrogateDiagonalTailChunk000Sub001Block113Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12930
    = surrogateDiagTailX0RatChunk000Sub001Block113Part003

theorem surrogateDiagonalTailChunk000Sub001Block113Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part003] using hcert

def TailChunk000Sub001Block113Part004SupportExplicit : Finset ℕ :=
  ([12931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part004 : ℚ :=
  (5057760856925 : ℚ) / 32238699947715723264

def SurrogateDiagonalTailChunk000Sub001Block113Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12931
    = surrogateDiagTailX0RatChunk000Sub001Block113Part004

theorem surrogateDiagonalTailChunk000Sub001Block113Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part004] using hcert

def TailChunk000Sub001Block113Part005SupportExplicit : Finset ℕ :=
  ([12934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part005 : ℚ :=
  (622186859425 : ℚ) / 933277704146145792

def SurrogateDiagonalTailChunk000Sub001Block113Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12934
    = surrogateDiagTailX0RatChunk000Sub001Block113Part005

theorem surrogateDiagonalTailChunk000Sub001Block113Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part005] using hcert

def TailChunk000Sub001Block113Part006SupportExplicit : Finset ℕ :=
  ([12935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part006 : ℚ :=
  (3108464455025 : ℚ) / 10200526155331928064

def SurrogateDiagonalTailChunk000Sub001Block113Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12935
    = surrogateDiagTailX0RatChunk000Sub001Block113Part006

theorem surrogateDiagonalTailChunk000Sub001Block113Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part006] using hcert

def TailChunk000Sub001Block113Part007SupportExplicit : Finset ℕ :=
  ([12937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part007 : ℚ :=
  (377123629717 : ℚ) / 2186860851049267200

def SurrogateDiagonalTailChunk000Sub001Block113Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12937
    = surrogateDiagTailX0RatChunk000Sub001Block113Part007

theorem surrogateDiagonalTailChunk000Sub001Block113Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part007] using hcert

def TailChunk000Sub001Block113Part008SupportExplicit : Finset ℕ :=
  ([12938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part008 : ℚ :=
  (653874390625 : ℚ) / 1094074541829495072

def SurrogateDiagonalTailChunk000Sub001Block113Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12938
    = surrogateDiagTailX0RatChunk000Sub001Block113Part008

theorem surrogateDiagonalTailChunk000Sub001Block113Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part008] using hcert

def TailChunk000Sub001Block113Part009SupportExplicit : Finset ℕ :=
  ([12939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part009 : ℚ :=
  (884119350275 : ℚ) / 1826078184564231168

def SurrogateDiagonalTailChunk000Sub001Block113Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12939
    = surrogateDiagTailX0RatChunk000Sub001Block113Part009

theorem surrogateDiagonalTailChunk000Sub001Block113Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part009] using hcert

def TailChunk000Sub001Block113Part010SupportExplicit : Finset ℕ :=
  ([12941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part010 : ℚ :=
  (4186737025 : ℚ) / 28042966652796192

def SurrogateDiagonalTailChunk000Sub001Block113Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12941
    = surrogateDiagTailX0RatChunk000Sub001Block113Part010

theorem surrogateDiagonalTailChunk000Sub001Block113Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part010] using hcert

def TailChunk000Sub001Block113Part011SupportExplicit : Finset ℕ :=
  ([12945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part011 : ℚ :=
  (4043371176475 : ℚ) / 5654782042247036928

def SurrogateDiagonalTailChunk000Sub001Block113Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12945
    = surrogateDiagTailX0RatChunk000Sub001Block113Part011

theorem surrogateDiagonalTailChunk000Sub001Block113Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part011] using hcert

def TailChunk000Sub001Block113Part012SupportExplicit : Finset ℕ :=
  ([12946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part012 : ℚ :=
  (654683265625 : ℚ) / 1096783483998392832

def SurrogateDiagonalTailChunk000Sub001Block113Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12946
    = surrogateDiagTailX0RatChunk000Sub001Block113Part012

theorem surrogateDiagonalTailChunk000Sub001Block113Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part012] using hcert

def TailChunk000Sub001Block113Part013SupportExplicit : Finset ℕ :=
  ([12949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part013 : ℚ :=
  (13713771375 : ℚ) / 4869468921815807584

def SurrogateDiagonalTailChunk000Sub001Block113Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12949
    = surrogateDiagTailX0RatChunk000Sub001Block113Part013

theorem surrogateDiagonalTailChunk000Sub001Block113Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part013] using hcert

def TailChunk000Sub001Block113Part014SupportExplicit : Finset ℕ :=
  ([12953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block113Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12953
    = surrogateDiagTailX0RatChunk000Sub001Block113Part014

theorem surrogateDiagonalTailChunk000Sub001Block113Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part014] using hcert

def TailChunk000Sub001Block113Part015SupportExplicit : Finset ℕ :=
  ([12954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part015 : ℚ :=
  (593288241475 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub001Block113Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12954
    = surrogateDiagTailX0RatChunk000Sub001Block113Part015

theorem surrogateDiagonalTailChunk000Sub001Block113Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part015] using hcert

def TailChunk000Sub001Block113Part016SupportExplicit : Finset ℕ :=
  ([12955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part016 : ℚ :=
  (33583805809 : ℚ) / 1152194696476723200

def SurrogateDiagonalTailChunk000Sub001Block113Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12955
    = surrogateDiagTailX0RatChunk000Sub001Block113Part016

theorem surrogateDiagonalTailChunk000Sub001Block113Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part016] using hcert

def TailChunk000Sub001Block113Part017SupportExplicit : Finset ℕ :=
  ([12957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part017 : ℚ :=
  (83281715225 : ℚ) / 533269390531756032

def SurrogateDiagonalTailChunk000Sub001Block113Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12957
    = surrogateDiagTailX0RatChunk000Sub001Block113Part017

theorem surrogateDiagonalTailChunk000Sub001Block113Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part017] using hcert

def TailChunk000Sub001Block113Part018SupportExplicit : Finset ℕ :=
  ([12958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part018 : ℚ :=
  (6127962947 : ℚ) / 42523783056000000

def SurrogateDiagonalTailChunk000Sub001Block113Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12958
    = surrogateDiagTailX0RatChunk000Sub001Block113Part018

theorem surrogateDiagonalTailChunk000Sub001Block113Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part018] using hcert

def TailChunk000Sub001Block113Part019SupportExplicit : Finset ℕ :=
  ([12959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block113Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12959
    = surrogateDiagTailX0RatChunk000Sub001Block113Part019

theorem surrogateDiagonalTailChunk000Sub001Block113Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part019] using hcert

def TailChunk000Sub001Block113Part020SupportExplicit : Finset ℕ :=
  ([12961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part020 : ℚ :=
  (34834423625 : ℚ) / 5669525165211942912

def SurrogateDiagonalTailChunk000Sub001Block113Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12961
    = surrogateDiagTailX0RatChunk000Sub001Block113Part020

theorem surrogateDiagonalTailChunk000Sub001Block113Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part020] using hcert

def TailChunk000Sub001Block113Part021SupportExplicit : Finset ℕ :=
  ([12962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block113Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12962
    = surrogateDiagTailX0RatChunk000Sub001Block113Part021

theorem surrogateDiagonalTailChunk000Sub001Block113Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part021] using hcert

def TailChunk000Sub001Block113Part022SupportExplicit : Finset ℕ :=
  ([12963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part022 : ℚ :=
  (24604775175 : ℚ) / 245801535248367616

def SurrogateDiagonalTailChunk000Sub001Block113Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12963
    = surrogateDiagTailX0RatChunk000Sub001Block113Part022

theorem surrogateDiagonalTailChunk000Sub001Block113Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part022] using hcert

def TailChunk000Sub001Block113Part023SupportExplicit : Finset ℕ :=
  ([12965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part023 : ℚ :=
  (280296795175 : ℚ) / 9631314361813303296

def SurrogateDiagonalTailChunk000Sub001Block113Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12965
    = surrogateDiagTailX0RatChunk000Sub001Block113Part023

theorem surrogateDiagonalTailChunk000Sub001Block113Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part023] using hcert

def TailChunk000Sub001Block113Part024SupportExplicit : Finset ℕ :=
  ([12966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block113Part024 : ℚ :=
  (11674165379 : ℚ) / 17417741539737600

def SurrogateDiagonalTailChunk000Sub001Block113Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12966
    = surrogateDiagTailX0RatChunk000Sub001Block113Part024

theorem surrogateDiagonalTailChunk000Sub001Block113Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block113Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block113Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block113Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block113Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block113Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block113Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block113HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block113Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block113Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block113Part000
    + surrogateDiagTailX0RatChunk000Sub001Block113Part001
    + surrogateDiagTailX0RatChunk000Sub001Block113Part002
    + surrogateDiagTailX0RatChunk000Sub001Block113Part003
    + surrogateDiagTailX0RatChunk000Sub001Block113Part004
    + surrogateDiagTailX0RatChunk000Sub001Block113Part005
    + surrogateDiagTailX0RatChunk000Sub001Block113Part006
    + surrogateDiagTailX0RatChunk000Sub001Block113Part007
    + surrogateDiagTailX0RatChunk000Sub001Block113Part008
    + surrogateDiagTailX0RatChunk000Sub001Block113Part009

def surrogateDiagonalTailChunk000Sub001Block113MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block113Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block113Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block113Part010
    + surrogateDiagTailX0RatChunk000Sub001Block113Part011
    + surrogateDiagTailX0RatChunk000Sub001Block113Part012
    + surrogateDiagTailX0RatChunk000Sub001Block113Part013
    + surrogateDiagTailX0RatChunk000Sub001Block113Part014
    + surrogateDiagTailX0RatChunk000Sub001Block113Part015
    + surrogateDiagTailX0RatChunk000Sub001Block113Part016
    + surrogateDiagTailX0RatChunk000Sub001Block113Part017
    + surrogateDiagTailX0RatChunk000Sub001Block113Part018
    + surrogateDiagTailX0RatChunk000Sub001Block113Part019

def surrogateDiagonalTailChunk000Sub001Block113TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block113Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block113Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block113Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block113Part020
    + surrogateDiagTailX0RatChunk000Sub001Block113Part021
    + surrogateDiagTailX0RatChunk000Sub001Block113Part022
    + surrogateDiagTailX0RatChunk000Sub001Block113Part023
    + surrogateDiagTailX0RatChunk000Sub001Block113Part024

def surrogateDiagonalTailChunk000Sub001Block113Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block113HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block113MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block113TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block113 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block113Part000
    + surrogateDiagTailX0RatChunk000Sub001Block113Part001
    + surrogateDiagTailX0RatChunk000Sub001Block113Part002
    + surrogateDiagTailX0RatChunk000Sub001Block113Part003
    + surrogateDiagTailX0RatChunk000Sub001Block113Part004
    + surrogateDiagTailX0RatChunk000Sub001Block113Part005
    + surrogateDiagTailX0RatChunk000Sub001Block113Part006
    + surrogateDiagTailX0RatChunk000Sub001Block113Part007
    + surrogateDiagTailX0RatChunk000Sub001Block113Part008
    + surrogateDiagTailX0RatChunk000Sub001Block113Part009
    + surrogateDiagTailX0RatChunk000Sub001Block113Part010
    + surrogateDiagTailX0RatChunk000Sub001Block113Part011
    + surrogateDiagTailX0RatChunk000Sub001Block113Part012
    + surrogateDiagTailX0RatChunk000Sub001Block113Part013
    + surrogateDiagTailX0RatChunk000Sub001Block113Part014
    + surrogateDiagTailX0RatChunk000Sub001Block113Part015
    + surrogateDiagTailX0RatChunk000Sub001Block113Part016
    + surrogateDiagTailX0RatChunk000Sub001Block113Part017
    + surrogateDiagTailX0RatChunk000Sub001Block113Part018
    + surrogateDiagTailX0RatChunk000Sub001Block113Part019
    + surrogateDiagTailX0RatChunk000Sub001Block113Part020
    + surrogateDiagTailX0RatChunk000Sub001Block113Part021
    + surrogateDiagTailX0RatChunk000Sub001Block113Part022
    + surrogateDiagTailX0RatChunk000Sub001Block113Part023
    + surrogateDiagTailX0RatChunk000Sub001Block113Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block113_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block113Head + surrogateDiagTailX0RatChunk000Sub001Block113Mid + surrogateDiagTailX0RatChunk000Sub001Block113Tail =
      surrogateDiagTailX0RatChunk000Sub001Block113 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block113Head surrogateDiagTailX0RatChunk000Sub001Block113Mid surrogateDiagTailX0RatChunk000Sub001Block113Tail surrogateDiagTailX0RatChunk000Sub001Block113
  ring

def SurrogateDiagonalTailChunk000Sub001Block113HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block113HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block113Head

def SurrogateDiagonalTailChunk000Sub001Block113MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block113MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block113Mid

def SurrogateDiagonalTailChunk000Sub001Block113TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block113TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block113Tail

theorem surrogateDiagonalTailChunk000Sub001Block113_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block113HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block113MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block113TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block113Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block113 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block113HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block113MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block113TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block113Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block113_eq_head_add_mid_add_tail

/-- Block 114 covers tail-support indices [7850,7875) and q from 12967 to 13007. -/

def TailChunk000Sub001Block114Part000SupportExplicit : Finset ℕ :=
  ([12967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block114Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12967
    = surrogateDiagTailX0RatChunk000Sub001Block114Part000

theorem surrogateDiagonalTailChunk000Sub001Block114Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part000] using hcert

def TailChunk000Sub001Block114Part001SupportExplicit : Finset ℕ :=
  ([12970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part001 : ℚ :=
  (210451010075 : ℚ) / 902935721419997184

def SurrogateDiagonalTailChunk000Sub001Block114Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12970
    = surrogateDiagTailX0RatChunk000Sub001Block114Part001

theorem surrogateDiagonalTailChunk000Sub001Block114Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part001] using hcert

def TailChunk000Sub001Block114Part002SupportExplicit : Finset ℕ :=
  ([12971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part002 : ℚ :=
  (774059773225 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk000Sub001Block114Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12971
    = surrogateDiagTailX0RatChunk000Sub001Block114Part002

theorem surrogateDiagonalTailChunk000Sub001Block114Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part002] using hcert

def TailChunk000Sub001Block114Part003SupportExplicit : Finset ℕ :=
  ([12973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block114Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12973
    = surrogateDiagTailX0RatChunk000Sub001Block114Part003

theorem surrogateDiagonalTailChunk000Sub001Block114Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part003] using hcert

def TailChunk000Sub001Block114Part004SupportExplicit : Finset ℕ :=
  ([12974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part004 : ℚ :=
  (1909341875 : ℚ) / 38422986812430336

def SurrogateDiagonalTailChunk000Sub001Block114Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12974
    = surrogateDiagTailX0RatChunk000Sub001Block114Part004

theorem surrogateDiagonalTailChunk000Sub001Block114Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part004] using hcert

def TailChunk000Sub001Block114Part005SupportExplicit : Finset ℕ :=
  ([12977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part005 : ℚ :=
  (208869763525 : ℚ) / 56787712887600655488

def SurrogateDiagonalTailChunk000Sub001Block114Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12977
    = surrogateDiagTailX0RatChunk000Sub001Block114Part005

theorem surrogateDiagonalTailChunk000Sub001Block114Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part005] using hcert

def TailChunk000Sub001Block114Part006SupportExplicit : Finset ℕ :=
  ([12979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block114Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12979
    = surrogateDiagTailX0RatChunk000Sub001Block114Part006

theorem surrogateDiagonalTailChunk000Sub001Block114Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part006] using hcert

def TailChunk000Sub001Block114Part007SupportExplicit : Finset ℕ :=
  ([12981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part007 : ℚ :=
  (83590523525 : ℚ) / 1000840488655476672

def SurrogateDiagonalTailChunk000Sub001Block114Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12981
    = surrogateDiagTailX0RatChunk000Sub001Block114Part007

theorem surrogateDiagonalTailChunk000Sub001Block114Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part007] using hcert

def TailChunk000Sub001Block114Part008SupportExplicit : Finset ℕ :=
  ([12982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block114Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12982
    = surrogateDiagTailX0RatChunk000Sub001Block114Part008

theorem surrogateDiagonalTailChunk000Sub001Block114Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part008] using hcert

def TailChunk000Sub001Block114Part009SupportExplicit : Finset ℕ :=
  ([12983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block114Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12983
    = surrogateDiagTailX0RatChunk000Sub001Block114Part009

theorem surrogateDiagonalTailChunk000Sub001Block114Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part009] using hcert

def TailChunk000Sub001Block114Part010SupportExplicit : Finset ℕ :=
  ([12986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part010 : ℚ :=
  (17572291 : ℚ) / 1167119377200000

def SurrogateDiagonalTailChunk000Sub001Block114Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12986
    = surrogateDiagTailX0RatChunk000Sub001Block114Part010

theorem surrogateDiagonalTailChunk000Sub001Block114Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part010] using hcert

def TailChunk000Sub001Block114Part011SupportExplicit : Finset ℕ :=
  ([12989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part011 : ℚ :=
  (2802286523 : ℚ) / 1236650565785025600

def SurrogateDiagonalTailChunk000Sub001Block114Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12989
    = surrogateDiagTailX0RatChunk000Sub001Block114Part011

theorem surrogateDiagonalTailChunk000Sub001Block114Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part011] using hcert

def TailChunk000Sub001Block114Part012SupportExplicit : Finset ℕ :=
  ([12990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part012 : ℚ :=
  (666227718275 : ℚ) / 178357673366913024

def SurrogateDiagonalTailChunk000Sub001Block114Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12990
    = surrogateDiagTailX0RatChunk000Sub001Block114Part012

theorem surrogateDiagonalTailChunk000Sub001Block114Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part012] using hcert

def TailChunk000Sub001Block114Part013SupportExplicit : Finset ℕ :=
  ([12991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part013 : ℚ :=
  (4680245943 : ℚ) / 646388505184000000

def SurrogateDiagonalTailChunk000Sub001Block114Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12991
    = surrogateDiagTailX0RatChunk000Sub001Block114Part013

theorem surrogateDiagonalTailChunk000Sub001Block114Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part013] using hcert

def TailChunk000Sub001Block114Part014SupportExplicit : Finset ℕ :=
  ([12993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part014 : ℚ :=
  (37818713 : ℚ) / 398376747417600

def SurrogateDiagonalTailChunk000Sub001Block114Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12993
    = surrogateDiagTailX0RatChunk000Sub001Block114Part014

theorem surrogateDiagonalTailChunk000Sub001Block114Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part014] using hcert

def TailChunk000Sub001Block114Part015SupportExplicit : Finset ℕ :=
  ([12994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part015 : ℚ :=
  (426442960925 : ℚ) / 671639582244077568

def SurrogateDiagonalTailChunk000Sub001Block114Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12994
    = surrogateDiagTailX0RatChunk000Sub001Block114Part015

theorem surrogateDiagonalTailChunk000Sub001Block114Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part015] using hcert

def TailChunk000Sub001Block114Part016SupportExplicit : Finset ℕ :=
  ([12995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part016 : ℚ :=
  (66139771175 : ℚ) / 1685394616989253632

def SurrogateDiagonalTailChunk000Sub001Block114Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12995
    = surrogateDiagTailX0RatChunk000Sub001Block114Part016

theorem surrogateDiagonalTailChunk000Sub001Block114Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part016] using hcert

def TailChunk000Sub001Block114Part017SupportExplicit : Finset ℕ :=
  ([12997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part017 : ℚ :=
  (298828581 : ℚ) / 170209535661178880

def SurrogateDiagonalTailChunk000Sub001Block114Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12997
    = surrogateDiagTailX0RatChunk000Sub001Block114Part017

theorem surrogateDiagonalTailChunk000Sub001Block114Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part017] using hcert

def TailChunk000Sub001Block114Part018SupportExplicit : Finset ℕ :=
  ([12998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part018 : ℚ :=
  (284374374125 : ℚ) / 447759721496051712

def SurrogateDiagonalTailChunk000Sub001Block114Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12998
    = surrogateDiagTailX0RatChunk000Sub001Block114Part018

theorem surrogateDiagonalTailChunk000Sub001Block114Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part018] using hcert

def TailChunk000Sub001Block114Part019SupportExplicit : Finset ℕ :=
  ([12999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part019 : ℚ :=
  (293375750575 : ℚ) / 1890800689938043392

def SurrogateDiagonalTailChunk000Sub001Block114Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12999
    = surrogateDiagTailX0RatChunk000Sub001Block114Part019

theorem surrogateDiagonalTailChunk000Sub001Block114Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part019] using hcert

def TailChunk000Sub001Block114Part020SupportExplicit : Finset ℕ :=
  ([13001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block114Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13001
    = surrogateDiagTailX0RatChunk000Sub001Block114Part020

theorem surrogateDiagonalTailChunk000Sub001Block114Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part020] using hcert

def TailChunk000Sub001Block114Part021SupportExplicit : Finset ℕ :=
  ([13002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part021 : ℚ :=
  (1033582887 : ℚ) / 393622457016320

def SurrogateDiagonalTailChunk000Sub001Block114Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13002
    = surrogateDiagTailX0RatChunk000Sub001Block114Part021

theorem surrogateDiagonalTailChunk000Sub001Block114Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part021] using hcert

def TailChunk000Sub001Block114Part022SupportExplicit : Finset ℕ :=
  ([13003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block114Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13003
    = surrogateDiagTailX0RatChunk000Sub001Block114Part022

theorem surrogateDiagonalTailChunk000Sub001Block114Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part022] using hcert

def TailChunk000Sub001Block114Part023SupportExplicit : Finset ℕ :=
  ([13006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part023 : ℚ :=
  (2155219612375 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk000Sub001Block114Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13006
    = surrogateDiagTailX0RatChunk000Sub001Block114Part023

theorem surrogateDiagonalTailChunk000Sub001Block114Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part023] using hcert

def TailChunk000Sub001Block114Part024SupportExplicit : Finset ℕ :=
  ([13007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block114Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block114Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13007
    = surrogateDiagTailX0RatChunk000Sub001Block114Part024

theorem surrogateDiagonalTailChunk000Sub001Block114Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block114Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block114Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block114Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block114Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block114Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block114Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block114HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block114Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block114Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block114Part000
    + surrogateDiagTailX0RatChunk000Sub001Block114Part001
    + surrogateDiagTailX0RatChunk000Sub001Block114Part002
    + surrogateDiagTailX0RatChunk000Sub001Block114Part003
    + surrogateDiagTailX0RatChunk000Sub001Block114Part004
    + surrogateDiagTailX0RatChunk000Sub001Block114Part005
    + surrogateDiagTailX0RatChunk000Sub001Block114Part006
    + surrogateDiagTailX0RatChunk000Sub001Block114Part007
    + surrogateDiagTailX0RatChunk000Sub001Block114Part008
    + surrogateDiagTailX0RatChunk000Sub001Block114Part009

def surrogateDiagonalTailChunk000Sub001Block114MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block114Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block114Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block114Part010
    + surrogateDiagTailX0RatChunk000Sub001Block114Part011
    + surrogateDiagTailX0RatChunk000Sub001Block114Part012
    + surrogateDiagTailX0RatChunk000Sub001Block114Part013
    + surrogateDiagTailX0RatChunk000Sub001Block114Part014
    + surrogateDiagTailX0RatChunk000Sub001Block114Part015
    + surrogateDiagTailX0RatChunk000Sub001Block114Part016
    + surrogateDiagTailX0RatChunk000Sub001Block114Part017
    + surrogateDiagTailX0RatChunk000Sub001Block114Part018
    + surrogateDiagTailX0RatChunk000Sub001Block114Part019

def surrogateDiagonalTailChunk000Sub001Block114TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block114Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block114Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block114Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block114Part020
    + surrogateDiagTailX0RatChunk000Sub001Block114Part021
    + surrogateDiagTailX0RatChunk000Sub001Block114Part022
    + surrogateDiagTailX0RatChunk000Sub001Block114Part023
    + surrogateDiagTailX0RatChunk000Sub001Block114Part024

def surrogateDiagonalTailChunk000Sub001Block114Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block114HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block114MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block114TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block114 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block114Part000
    + surrogateDiagTailX0RatChunk000Sub001Block114Part001
    + surrogateDiagTailX0RatChunk000Sub001Block114Part002
    + surrogateDiagTailX0RatChunk000Sub001Block114Part003
    + surrogateDiagTailX0RatChunk000Sub001Block114Part004
    + surrogateDiagTailX0RatChunk000Sub001Block114Part005
    + surrogateDiagTailX0RatChunk000Sub001Block114Part006
    + surrogateDiagTailX0RatChunk000Sub001Block114Part007
    + surrogateDiagTailX0RatChunk000Sub001Block114Part008
    + surrogateDiagTailX0RatChunk000Sub001Block114Part009
    + surrogateDiagTailX0RatChunk000Sub001Block114Part010
    + surrogateDiagTailX0RatChunk000Sub001Block114Part011
    + surrogateDiagTailX0RatChunk000Sub001Block114Part012
    + surrogateDiagTailX0RatChunk000Sub001Block114Part013
    + surrogateDiagTailX0RatChunk000Sub001Block114Part014
    + surrogateDiagTailX0RatChunk000Sub001Block114Part015
    + surrogateDiagTailX0RatChunk000Sub001Block114Part016
    + surrogateDiagTailX0RatChunk000Sub001Block114Part017
    + surrogateDiagTailX0RatChunk000Sub001Block114Part018
    + surrogateDiagTailX0RatChunk000Sub001Block114Part019
    + surrogateDiagTailX0RatChunk000Sub001Block114Part020
    + surrogateDiagTailX0RatChunk000Sub001Block114Part021
    + surrogateDiagTailX0RatChunk000Sub001Block114Part022
    + surrogateDiagTailX0RatChunk000Sub001Block114Part023
    + surrogateDiagTailX0RatChunk000Sub001Block114Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block114_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block114Head + surrogateDiagTailX0RatChunk000Sub001Block114Mid + surrogateDiagTailX0RatChunk000Sub001Block114Tail =
      surrogateDiagTailX0RatChunk000Sub001Block114 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block114Head surrogateDiagTailX0RatChunk000Sub001Block114Mid surrogateDiagTailX0RatChunk000Sub001Block114Tail surrogateDiagTailX0RatChunk000Sub001Block114
  ring

def SurrogateDiagonalTailChunk000Sub001Block114HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block114HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block114Head

def SurrogateDiagonalTailChunk000Sub001Block114MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block114MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block114Mid

def SurrogateDiagonalTailChunk000Sub001Block114TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block114TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block114Tail

theorem surrogateDiagonalTailChunk000Sub001Block114_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block114HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block114MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block114TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block114Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block114 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block114HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block114MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block114TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block114Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block114_eq_head_add_mid_add_tail

/-- Block 115 covers tail-support indices [7875,7900) and q from 13009 to 13049. -/

def TailChunk000Sub001Block115Part000SupportExplicit : Finset ℕ :=
  ([13009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block115Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13009
    = surrogateDiagTailX0RatChunk000Sub001Block115Part000

theorem surrogateDiagonalTailChunk000Sub001Block115Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part000] using hcert

def TailChunk000Sub001Block115Part001SupportExplicit : Finset ℕ :=
  ([13010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part001 : ℚ :=
  (40170108197 : ℚ) / 36565391616000000

def SurrogateDiagonalTailChunk000Sub001Block115Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13010
    = surrogateDiagTailX0RatChunk000Sub001Block115Part001

theorem surrogateDiagonalTailChunk000Sub001Block115Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part001] using hcert

def TailChunk000Sub001Block115Part002SupportExplicit : Finset ℕ :=
  ([13011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part002 : ℚ :=
  (293920269775 : ℚ) / 3535443851408965632

def SurrogateDiagonalTailChunk000Sub001Block115Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13011
    = surrogateDiagTailX0RatChunk000Sub001Block115Part002

theorem surrogateDiagonalTailChunk000Sub001Block115Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part002] using hcert

def TailChunk000Sub001Block115Part003SupportExplicit : Finset ℕ :=
  ([13015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part003 : ℚ :=
  (18633894425 : ℚ) / 450756815458664448

def SurrogateDiagonalTailChunk000Sub001Block115Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13015
    = surrogateDiagTailX0RatChunk000Sub001Block115Part003

theorem surrogateDiagonalTailChunk000Sub001Block115Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part003] using hcert

def TailChunk000Sub001Block115Part004SupportExplicit : Finset ℕ :=
  ([13017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part004 : ℚ :=
  (588382664525 : ℚ) / 7083942650099694144

def SurrogateDiagonalTailChunk000Sub001Block115Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13017
    = surrogateDiagTailX0RatChunk000Sub001Block115Part004

theorem surrogateDiagonalTailChunk000Sub001Block115Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part004] using hcert

def TailChunk000Sub001Block115Part005SupportExplicit : Finset ℕ :=
  ([13018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part005 : ℚ :=
  (92496340375 : ℚ) / 137198780549576064

def SurrogateDiagonalTailChunk000Sub001Block115Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13018
    = surrogateDiagTailX0RatChunk000Sub001Block115Part005

theorem surrogateDiagonalTailChunk000Sub001Block115Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part005] using hcert

def TailChunk000Sub001Block115Part006SupportExplicit : Finset ℕ :=
  ([13019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part006 : ℚ :=
  (49866464075 : ℚ) / 32483627242099467264

def SurrogateDiagonalTailChunk000Sub001Block115Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13019
    = surrogateDiagTailX0RatChunk000Sub001Block115Part006

theorem surrogateDiagonalTailChunk000Sub001Block115Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part006] using hcert

def TailChunk000Sub001Block115Part007SupportExplicit : Finset ℕ :=
  ([13021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part007 : ℚ :=
  (48813049725 : ℚ) / 20637153074417238016

def SurrogateDiagonalTailChunk000Sub001Block115Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13021
    = surrogateDiagTailX0RatChunk000Sub001Block115Part007

theorem surrogateDiagonalTailChunk000Sub001Block115Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part007] using hcert

def TailChunk000Sub001Block115Part008SupportExplicit : Finset ℕ :=
  ([13022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part008 : ℚ :=
  (2449668826375 : ℚ) / 3489476204749651968

def SurrogateDiagonalTailChunk000Sub001Block115Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13022
    = surrogateDiagTailX0RatChunk000Sub001Block115Part008

theorem surrogateDiagonalTailChunk000Sub001Block115Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part008] using hcert

def TailChunk000Sub001Block115Part009SupportExplicit : Finset ℕ :=
  ([13026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part009 : ℚ :=
  (1335492431875 : ℚ) / 629947240579104768

def SurrogateDiagonalTailChunk000Sub001Block115Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13026
    = surrogateDiagTailX0RatChunk000Sub001Block115Part009

theorem surrogateDiagonalTailChunk000Sub001Block115Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part009] using hcert

def TailChunk000Sub001Block115Part010SupportExplicit : Finset ℕ :=
  ([13027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part010 : ℚ :=
  (481696411 : ℚ) / 28730942223436800

def SurrogateDiagonalTailChunk000Sub001Block115Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13027
    = surrogateDiagTailX0RatChunk000Sub001Block115Part010

theorem surrogateDiagonalTailChunk000Sub001Block115Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part010] using hcert

def TailChunk000Sub001Block115Part011SupportExplicit : Finset ℕ :=
  ([13029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part011 : ℚ :=
  (47577648901 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk000Sub001Block115Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13029
    = surrogateDiagTailX0RatChunk000Sub001Block115Part011

theorem surrogateDiagonalTailChunk000Sub001Block115Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part011] using hcert

def TailChunk000Sub001Block115Part012SupportExplicit : Finset ℕ :=
  ([13030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part012 : ℚ :=
  (167890527575 : ℚ) / 153295538396603904

def SurrogateDiagonalTailChunk000Sub001Block115Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13030
    = surrogateDiagTailX0RatChunk000Sub001Block115Part012

theorem surrogateDiagonalTailChunk000Sub001Block115Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part012] using hcert

def TailChunk000Sub001Block115Part013SupportExplicit : Finset ℕ :=
  ([13031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part013 : ℚ :=
  (36947888075 : ℚ) / 33477318655343207424

def SurrogateDiagonalTailChunk000Sub001Block115Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13031
    = surrogateDiagTailX0RatChunk000Sub001Block115Part013

theorem surrogateDiagonalTailChunk000Sub001Block115Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part013] using hcert

def TailChunk000Sub001Block115Part014SupportExplicit : Finset ℕ :=
  ([13033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block115Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13033
    = surrogateDiagTailX0RatChunk000Sub001Block115Part014

theorem surrogateDiagonalTailChunk000Sub001Block115Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part014] using hcert

def TailChunk000Sub001Block115Part015SupportExplicit : Finset ℕ :=
  ([13035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part015 : ℚ :=
  (693714923 : ℚ) / 2106166557081600

def SurrogateDiagonalTailChunk000Sub001Block115Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13035
    = surrogateDiagTailX0RatChunk000Sub001Block115Part015

theorem surrogateDiagonalTailChunk000Sub001Block115Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part015] using hcert

def TailChunk000Sub001Block115Part016SupportExplicit : Finset ℕ :=
  ([13037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block115Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13037
    = surrogateDiagTailX0RatChunk000Sub001Block115Part016

theorem surrogateDiagonalTailChunk000Sub001Block115Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part016] using hcert

def TailChunk000Sub001Block115Part017SupportExplicit : Finset ℕ :=
  ([13038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part017 : ℚ :=
  (18772710819 : ℚ) / 9984789603942400

def SurrogateDiagonalTailChunk000Sub001Block115Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13038
    = surrogateDiagTailX0RatChunk000Sub001Block115Part017

theorem surrogateDiagonalTailChunk000Sub001Block115Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part017] using hcert

def TailChunk000Sub001Block115Part018SupportExplicit : Finset ℕ :=
  ([13039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part018 : ℚ :=
  (34803149425 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk000Sub001Block115Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13039
    = surrogateDiagTailX0RatChunk000Sub001Block115Part018

theorem surrogateDiagonalTailChunk000Sub001Block115Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part018] using hcert

def TailChunk000Sub001Block115Part019SupportExplicit : Finset ℕ :=
  ([13042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part019 : ℚ :=
  (1063086025 : ℚ) / 1807495534981632

def SurrogateDiagonalTailChunk000Sub001Block115Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13042
    = surrogateDiagTailX0RatChunk000Sub001Block115Part019

theorem surrogateDiagonalTailChunk000Sub001Block115Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part019] using hcert

def TailChunk000Sub001Block115Part020SupportExplicit : Finset ℕ :=
  ([13043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block115Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13043
    = surrogateDiagTailX0RatChunk000Sub001Block115Part020

theorem surrogateDiagonalTailChunk000Sub001Block115Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part020] using hcert

def TailChunk000Sub001Block115Part021SupportExplicit : Finset ℕ :=
  ([13045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part021 : ℚ :=
  (851288300725 : ℚ) / 29614006845139058688

def SurrogateDiagonalTailChunk000Sub001Block115Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13045
    = surrogateDiagTailX0RatChunk000Sub001Block115Part021

theorem surrogateDiagonalTailChunk000Sub001Block115Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part021] using hcert

def TailChunk000Sub001Block115Part022SupportExplicit : Finset ℕ :=
  ([13046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part022 : ℚ :=
  (93891166981 : ℚ) / 122849580299059200

def SurrogateDiagonalTailChunk000Sub001Block115Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13046
    = surrogateDiagTailX0RatChunk000Sub001Block115Part022

theorem surrogateDiagonalTailChunk000Sub001Block115Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part022] using hcert

def TailChunk000Sub001Block115Part023SupportExplicit : Finset ℕ :=
  ([13047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part023 : ℚ :=
  (1181645031275 : ℚ) / 7149488756845323264

def SurrogateDiagonalTailChunk000Sub001Block115Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13047
    = surrogateDiagTailX0RatChunk000Sub001Block115Part023

theorem surrogateDiagonalTailChunk000Sub001Block115Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part023] using hcert

def TailChunk000Sub001Block115Part024SupportExplicit : Finset ℕ :=
  ([13049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block115Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block115Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13049
    = surrogateDiagTailX0RatChunk000Sub001Block115Part024

theorem surrogateDiagonalTailChunk000Sub001Block115Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block115Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block115Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block115Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block115Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block115Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block115Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block115HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block115Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block115Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block115Part000
    + surrogateDiagTailX0RatChunk000Sub001Block115Part001
    + surrogateDiagTailX0RatChunk000Sub001Block115Part002
    + surrogateDiagTailX0RatChunk000Sub001Block115Part003
    + surrogateDiagTailX0RatChunk000Sub001Block115Part004
    + surrogateDiagTailX0RatChunk000Sub001Block115Part005
    + surrogateDiagTailX0RatChunk000Sub001Block115Part006
    + surrogateDiagTailX0RatChunk000Sub001Block115Part007
    + surrogateDiagTailX0RatChunk000Sub001Block115Part008
    + surrogateDiagTailX0RatChunk000Sub001Block115Part009

def surrogateDiagonalTailChunk000Sub001Block115MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block115Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block115Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block115Part010
    + surrogateDiagTailX0RatChunk000Sub001Block115Part011
    + surrogateDiagTailX0RatChunk000Sub001Block115Part012
    + surrogateDiagTailX0RatChunk000Sub001Block115Part013
    + surrogateDiagTailX0RatChunk000Sub001Block115Part014
    + surrogateDiagTailX0RatChunk000Sub001Block115Part015
    + surrogateDiagTailX0RatChunk000Sub001Block115Part016
    + surrogateDiagTailX0RatChunk000Sub001Block115Part017
    + surrogateDiagTailX0RatChunk000Sub001Block115Part018
    + surrogateDiagTailX0RatChunk000Sub001Block115Part019

def surrogateDiagonalTailChunk000Sub001Block115TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block115Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block115Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block115Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block115Part020
    + surrogateDiagTailX0RatChunk000Sub001Block115Part021
    + surrogateDiagTailX0RatChunk000Sub001Block115Part022
    + surrogateDiagTailX0RatChunk000Sub001Block115Part023
    + surrogateDiagTailX0RatChunk000Sub001Block115Part024

def surrogateDiagonalTailChunk000Sub001Block115Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block115HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block115MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block115TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block115 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block115Part000
    + surrogateDiagTailX0RatChunk000Sub001Block115Part001
    + surrogateDiagTailX0RatChunk000Sub001Block115Part002
    + surrogateDiagTailX0RatChunk000Sub001Block115Part003
    + surrogateDiagTailX0RatChunk000Sub001Block115Part004
    + surrogateDiagTailX0RatChunk000Sub001Block115Part005
    + surrogateDiagTailX0RatChunk000Sub001Block115Part006
    + surrogateDiagTailX0RatChunk000Sub001Block115Part007
    + surrogateDiagTailX0RatChunk000Sub001Block115Part008
    + surrogateDiagTailX0RatChunk000Sub001Block115Part009
    + surrogateDiagTailX0RatChunk000Sub001Block115Part010
    + surrogateDiagTailX0RatChunk000Sub001Block115Part011
    + surrogateDiagTailX0RatChunk000Sub001Block115Part012
    + surrogateDiagTailX0RatChunk000Sub001Block115Part013
    + surrogateDiagTailX0RatChunk000Sub001Block115Part014
    + surrogateDiagTailX0RatChunk000Sub001Block115Part015
    + surrogateDiagTailX0RatChunk000Sub001Block115Part016
    + surrogateDiagTailX0RatChunk000Sub001Block115Part017
    + surrogateDiagTailX0RatChunk000Sub001Block115Part018
    + surrogateDiagTailX0RatChunk000Sub001Block115Part019
    + surrogateDiagTailX0RatChunk000Sub001Block115Part020
    + surrogateDiagTailX0RatChunk000Sub001Block115Part021
    + surrogateDiagTailX0RatChunk000Sub001Block115Part022
    + surrogateDiagTailX0RatChunk000Sub001Block115Part023
    + surrogateDiagTailX0RatChunk000Sub001Block115Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block115_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block115Head + surrogateDiagTailX0RatChunk000Sub001Block115Mid + surrogateDiagTailX0RatChunk000Sub001Block115Tail =
      surrogateDiagTailX0RatChunk000Sub001Block115 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block115Head surrogateDiagTailX0RatChunk000Sub001Block115Mid surrogateDiagTailX0RatChunk000Sub001Block115Tail surrogateDiagTailX0RatChunk000Sub001Block115
  ring

def SurrogateDiagonalTailChunk000Sub001Block115HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block115HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block115Head

def SurrogateDiagonalTailChunk000Sub001Block115MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block115MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block115Mid

def SurrogateDiagonalTailChunk000Sub001Block115TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block115TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block115Tail

theorem surrogateDiagonalTailChunk000Sub001Block115_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block115HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block115MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block115TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block115Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block115 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block115HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block115MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block115TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block115Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block115_eq_head_add_mid_add_tail

/-- Block 116 covers tail-support indices [7900,7925) and q from 13051 to 13090. -/

def TailChunk000Sub001Block116Part000SupportExplicit : Finset ℕ :=
  ([13051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part000 : ℚ :=
  (2827371191 : ℚ) / 1260488927376000000

def SurrogateDiagonalTailChunk000Sub001Block116Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13051
    = surrogateDiagTailX0RatChunk000Sub001Block116Part000

theorem surrogateDiagonalTailChunk000Sub001Block116Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part000] using hcert

def TailChunk000Sub001Block116Part001SupportExplicit : Finset ℕ :=
  ([13053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part001 : ℚ :=
  (2258927417725 : ℚ) / 11349487476000718848

def SurrogateDiagonalTailChunk000Sub001Block116Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13053
    = surrogateDiagTailX0RatChunk000Sub001Block116Part001

theorem surrogateDiagonalTailChunk000Sub001Block116Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part001] using hcert

def TailChunk000Sub001Block116Part002SupportExplicit : Finset ℕ :=
  ([13054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part002 : ℚ :=
  (1719613891 : ℚ) / 2727495623646720

def SurrogateDiagonalTailChunk000Sub001Block116Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13054
    = surrogateDiagTailX0RatChunk000Sub001Block116Part002

theorem surrogateDiagonalTailChunk000Sub001Block116Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part002] using hcert

def TailChunk000Sub001Block116Part003SupportExplicit : Finset ℕ :=
  ([13055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part003 : ℚ :=
  (492410613275 : ℚ) / 7943530905935806464

def SurrogateDiagonalTailChunk000Sub001Block116Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13055
    = surrogateDiagTailX0RatChunk000Sub001Block116Part003

theorem surrogateDiagonalTailChunk000Sub001Block116Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part003] using hcert

def TailChunk000Sub001Block116Part004SupportExplicit : Finset ℕ :=
  ([13057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part004 : ℚ :=
  (4727537487 : ℚ) / 659636003225814400

def SurrogateDiagonalTailChunk000Sub001Block116Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13057
    = surrogateDiagTailX0RatChunk000Sub001Block116Part004

theorem surrogateDiagonalTailChunk000Sub001Block116Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part004] using hcert

def TailChunk000Sub001Block116Part005SupportExplicit : Finset ℕ :=
  ([13058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part005 : ℚ :=
  (666060015625 : ℚ) / 1135239387081080832

def SurrogateDiagonalTailChunk000Sub001Block116Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13058
    = surrogateDiagTailX0RatChunk000Sub001Block116Part005

theorem surrogateDiagonalTailChunk000Sub001Block116Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part005] using hcert

def TailChunk000Sub001Block116Part006SupportExplicit : Finset ℕ :=
  ([13061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part006 : ℚ :=
  (5426074075 : ℚ) / 2930790904337793024

def SurrogateDiagonalTailChunk000Sub001Block116Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13061
    = surrogateDiagTailX0RatChunk000Sub001Block116Part006

theorem surrogateDiagonalTailChunk000Sub001Block116Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part006] using hcert

def TailChunk000Sub001Block116Part007SupportExplicit : Finset ℕ :=
  ([13062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part007 : ℚ :=
  (1574079557 : ℚ) / 598561296321600

def SurrogateDiagonalTailChunk000Sub001Block116Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13062
    = surrogateDiagTailX0RatChunk000Sub001Block116Part007

theorem surrogateDiagonalTailChunk000Sub001Block116Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part007] using hcert

def TailChunk000Sub001Block116Part008SupportExplicit : Finset ℕ :=
  ([13063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block116Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13063
    = surrogateDiagTailX0RatChunk000Sub001Block116Part008

theorem surrogateDiagonalTailChunk000Sub001Block116Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part008] using hcert

def TailChunk000Sub001Block116Part009SupportExplicit : Finset ℕ :=
  ([13065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part009 : ℚ :=
  (1204969646725 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk000Sub001Block116Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13065
    = surrogateDiagTailX0RatChunk000Sub001Block116Part009

theorem surrogateDiagonalTailChunk000Sub001Block116Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part009] using hcert

def TailChunk000Sub001Block116Part010SupportExplicit : Finset ℕ :=
  ([13066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part010 : ℚ :=
  (143050148875 : ℚ) / 225580744736801856

def SurrogateDiagonalTailChunk000Sub001Block116Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13066
    = surrogateDiagTailX0RatChunk000Sub001Block116Part010

theorem surrogateDiagonalTailChunk000Sub001Block116Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part010] using hcert

def TailChunk000Sub001Block116Part011SupportExplicit : Finset ℕ :=
  ([13067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part011 : ℚ :=
  (2421616775 : ℚ) / 2108078968676557824

def SurrogateDiagonalTailChunk000Sub001Block116Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13067
    = surrogateDiagTailX0RatChunk000Sub001Block116Part011

theorem surrogateDiagonalTailChunk000Sub001Block116Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part011] using hcert

def TailChunk000Sub001Block116Part012SupportExplicit : Finset ℕ :=
  ([13069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part012 : ℚ :=
  (12120004225 : ℚ) / 727586543367191232

def SurrogateDiagonalTailChunk000Sub001Block116Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13069
    = surrogateDiagTailX0RatChunk000Sub001Block116Part012

theorem surrogateDiagonalTailChunk000Sub001Block116Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part012] using hcert

def TailChunk000Sub001Block116Part013SupportExplicit : Finset ℕ :=
  ([13070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part013 : ℚ :=
  (7918268275 : ℚ) / 7274440008322248

def SurrogateDiagonalTailChunk000Sub001Block116Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13070
    = surrogateDiagTailX0RatChunk000Sub001Block116Part013

theorem surrogateDiagonalTailChunk000Sub001Block116Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part013] using hcert

def TailChunk000Sub001Block116Part014SupportExplicit : Finset ℕ :=
  ([13071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part014 : ℚ :=
  (148318259825 : ℚ) / 1800563071954749696

def SurrogateDiagonalTailChunk000Sub001Block116Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13071
    = surrogateDiagTailX0RatChunk000Sub001Block116Part014

theorem surrogateDiagonalTailChunk000Sub001Block116Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part014] using hcert

def TailChunk000Sub001Block116Part015SupportExplicit : Finset ℕ :=
  ([13073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part015 : ℚ :=
  (12553404575 : ℚ) / 3167226806692478976

def SurrogateDiagonalTailChunk000Sub001Block116Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13073
    = surrogateDiagTailX0RatChunk000Sub001Block116Part015

theorem surrogateDiagonalTailChunk000Sub001Block116Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part015] using hcert

def TailChunk000Sub001Block116Part016SupportExplicit : Finset ℕ :=
  ([13074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part016 : ℚ :=
  (92703957325 : ℚ) / 56267595998585928

def SurrogateDiagonalTailChunk000Sub001Block116Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13074
    = surrogateDiagTailX0RatChunk000Sub001Block116Part016

theorem surrogateDiagonalTailChunk000Sub001Block116Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part016] using hcert

def TailChunk000Sub001Block116Part017SupportExplicit : Finset ℕ :=
  ([13078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part017 : ℚ :=
  (149888197225 : ℚ) / 205800643790218368

def SurrogateDiagonalTailChunk000Sub001Block116Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13078
    = surrogateDiagTailX0RatChunk000Sub001Block116Part017

theorem surrogateDiagonalTailChunk000Sub001Block116Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part017] using hcert

def TailChunk000Sub001Block116Part018SupportExplicit : Finset ℕ :=
  ([13079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part018 : ℚ :=
  (6972054087 : ℚ) / 524611354624000000

def SurrogateDiagonalTailChunk000Sub001Block116Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13079
    = surrogateDiagTailX0RatChunk000Sub001Block116Part018

theorem surrogateDiagonalTailChunk000Sub001Block116Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part018] using hcert

def TailChunk000Sub001Block116Part019SupportExplicit : Finset ℕ :=
  ([13081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part019 : ℚ :=
  (863349175 : ℚ) / 842218365626967168

def SurrogateDiagonalTailChunk000Sub001Block116Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13081
    = surrogateDiagTailX0RatChunk000Sub001Block116Part019

theorem surrogateDiagonalTailChunk000Sub001Block116Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part019] using hcert

def TailChunk000Sub001Block116Part020SupportExplicit : Finset ℕ :=
  ([13082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part020 : ℚ :=
  (51076056737 : ℚ) / 78780557961000000

def SurrogateDiagonalTailChunk000Sub001Block116Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13082
    = surrogateDiagTailX0RatChunk000Sub001Block116Part020

theorem surrogateDiagonalTailChunk000Sub001Block116Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part020] using hcert

def TailChunk000Sub001Block116Part021SupportExplicit : Finset ℕ :=
  ([13085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part021 : ℚ :=
  (428966860375 : ℚ) / 29979044225242103808

def SurrogateDiagonalTailChunk000Sub001Block116Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13085
    = surrogateDiagTailX0RatChunk000Sub001Block116Part021

theorem surrogateDiagonalTailChunk000Sub001Block116Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part021] using hcert

def TailChunk000Sub001Block116Part022SupportExplicit : Finset ℕ :=
  ([13087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part022 : ℚ :=
  (188049826225 : ℚ) / 60969260155749040128

def SurrogateDiagonalTailChunk000Sub001Block116Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13087
    = surrogateDiagTailX0RatChunk000Sub001Block116Part022

theorem surrogateDiagonalTailChunk000Sub001Block116Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part022] using hcert

def TailChunk000Sub001Block116Part023SupportExplicit : Finset ℕ :=
  ([13089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part023 : ℚ :=
  (594907664225 : ℚ) / 7242016181172231744

def SurrogateDiagonalTailChunk000Sub001Block116Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13089
    = surrogateDiagTailX0RatChunk000Sub001Block116Part023

theorem surrogateDiagonalTailChunk000Sub001Block116Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part023] using hcert

def TailChunk000Sub001Block116Part024SupportExplicit : Finset ℕ :=
  ([13090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block116Part024 : ℚ :=
  (11346790721 : ℚ) / 4349524118077440

def SurrogateDiagonalTailChunk000Sub001Block116Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13090
    = surrogateDiagTailX0RatChunk000Sub001Block116Part024

theorem surrogateDiagonalTailChunk000Sub001Block116Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block116Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block116Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block116Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block116Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block116Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block116Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block116HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block116Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block116Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block116Part000
    + surrogateDiagTailX0RatChunk000Sub001Block116Part001
    + surrogateDiagTailX0RatChunk000Sub001Block116Part002
    + surrogateDiagTailX0RatChunk000Sub001Block116Part003
    + surrogateDiagTailX0RatChunk000Sub001Block116Part004
    + surrogateDiagTailX0RatChunk000Sub001Block116Part005
    + surrogateDiagTailX0RatChunk000Sub001Block116Part006
    + surrogateDiagTailX0RatChunk000Sub001Block116Part007
    + surrogateDiagTailX0RatChunk000Sub001Block116Part008
    + surrogateDiagTailX0RatChunk000Sub001Block116Part009

def surrogateDiagonalTailChunk000Sub001Block116MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block116Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block116Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block116Part010
    + surrogateDiagTailX0RatChunk000Sub001Block116Part011
    + surrogateDiagTailX0RatChunk000Sub001Block116Part012
    + surrogateDiagTailX0RatChunk000Sub001Block116Part013
    + surrogateDiagTailX0RatChunk000Sub001Block116Part014
    + surrogateDiagTailX0RatChunk000Sub001Block116Part015
    + surrogateDiagTailX0RatChunk000Sub001Block116Part016
    + surrogateDiagTailX0RatChunk000Sub001Block116Part017
    + surrogateDiagTailX0RatChunk000Sub001Block116Part018
    + surrogateDiagTailX0RatChunk000Sub001Block116Part019

def surrogateDiagonalTailChunk000Sub001Block116TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block116Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block116Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block116Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block116Part020
    + surrogateDiagTailX0RatChunk000Sub001Block116Part021
    + surrogateDiagTailX0RatChunk000Sub001Block116Part022
    + surrogateDiagTailX0RatChunk000Sub001Block116Part023
    + surrogateDiagTailX0RatChunk000Sub001Block116Part024

def surrogateDiagonalTailChunk000Sub001Block116Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block116HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block116MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block116TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block116 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block116Part000
    + surrogateDiagTailX0RatChunk000Sub001Block116Part001
    + surrogateDiagTailX0RatChunk000Sub001Block116Part002
    + surrogateDiagTailX0RatChunk000Sub001Block116Part003
    + surrogateDiagTailX0RatChunk000Sub001Block116Part004
    + surrogateDiagTailX0RatChunk000Sub001Block116Part005
    + surrogateDiagTailX0RatChunk000Sub001Block116Part006
    + surrogateDiagTailX0RatChunk000Sub001Block116Part007
    + surrogateDiagTailX0RatChunk000Sub001Block116Part008
    + surrogateDiagTailX0RatChunk000Sub001Block116Part009
    + surrogateDiagTailX0RatChunk000Sub001Block116Part010
    + surrogateDiagTailX0RatChunk000Sub001Block116Part011
    + surrogateDiagTailX0RatChunk000Sub001Block116Part012
    + surrogateDiagTailX0RatChunk000Sub001Block116Part013
    + surrogateDiagTailX0RatChunk000Sub001Block116Part014
    + surrogateDiagTailX0RatChunk000Sub001Block116Part015
    + surrogateDiagTailX0RatChunk000Sub001Block116Part016
    + surrogateDiagTailX0RatChunk000Sub001Block116Part017
    + surrogateDiagTailX0RatChunk000Sub001Block116Part018
    + surrogateDiagTailX0RatChunk000Sub001Block116Part019
    + surrogateDiagTailX0RatChunk000Sub001Block116Part020
    + surrogateDiagTailX0RatChunk000Sub001Block116Part021
    + surrogateDiagTailX0RatChunk000Sub001Block116Part022
    + surrogateDiagTailX0RatChunk000Sub001Block116Part023
    + surrogateDiagTailX0RatChunk000Sub001Block116Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block116_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block116Head + surrogateDiagTailX0RatChunk000Sub001Block116Mid + surrogateDiagTailX0RatChunk000Sub001Block116Tail =
      surrogateDiagTailX0RatChunk000Sub001Block116 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block116Head surrogateDiagTailX0RatChunk000Sub001Block116Mid surrogateDiagTailX0RatChunk000Sub001Block116Tail surrogateDiagTailX0RatChunk000Sub001Block116
  ring

def SurrogateDiagonalTailChunk000Sub001Block116HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block116HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block116Head

def SurrogateDiagonalTailChunk000Sub001Block116MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block116MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block116Mid

def SurrogateDiagonalTailChunk000Sub001Block116TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block116TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block116Tail

theorem surrogateDiagonalTailChunk000Sub001Block116_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block116HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block116MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block116TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block116Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block116 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block116HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block116MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block116TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block116Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block116_eq_head_add_mid_add_tail

/-- Block 117 covers tail-support indices [7925,7950) and q from 13091 to 13129. -/

def TailChunk000Sub001Block117Part000SupportExplicit : Finset ℕ :=
  ([13091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part000 : ℚ :=
  (40354624975 : ℚ) / 3061342253024280576

def SurrogateDiagonalTailChunk000Sub001Block117Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13091
    = surrogateDiagTailX0RatChunk000Sub001Block117Part000

theorem surrogateDiagonalTailChunk000Sub001Block117Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part000] using hcert

def TailChunk000Sub001Block117Part001SupportExplicit : Finset ℕ :=
  ([13093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block117Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13093
    = surrogateDiagTailX0RatChunk000Sub001Block117Part001

theorem surrogateDiagonalTailChunk000Sub001Block117Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part001] using hcert

def TailChunk000Sub001Block117Part002SupportExplicit : Finset ℕ :=
  ([13094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part002 : ℚ :=
  (669737640625 : ℚ) / 1147812292313561682

def SurrogateDiagonalTailChunk000Sub001Block117Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13094
    = surrogateDiagTailX0RatChunk000Sub001Block117Part002

theorem surrogateDiagonalTailChunk000Sub001Block117Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part002] using hcert

def TailChunk000Sub001Block117Part003SupportExplicit : Finset ℕ :=
  ([13097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part003 : ℚ :=
  (8777997167 : ℚ) / 792552941620545600

def SurrogateDiagonalTailChunk000Sub001Block117Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13097
    = surrogateDiagTailX0RatChunk000Sub001Block117Part003

theorem surrogateDiagonalTailChunk000Sub001Block117Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part003] using hcert

def TailChunk000Sub001Block117Part004SupportExplicit : Finset ℕ :=
  ([13098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part004 : ℚ :=
  (177478147325 : ℚ) / 95055846095425536

def SurrogateDiagonalTailChunk000Sub001Block117Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13098
    = surrogateDiagTailX0RatChunk000Sub001Block117Part004

theorem surrogateDiagonalTailChunk000Sub001Block117Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part004] using hcert

def TailChunk000Sub001Block117Part005SupportExplicit : Finset ℕ :=
  ([13099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block117Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13099
    = surrogateDiagTailX0RatChunk000Sub001Block117Part005

theorem surrogateDiagonalTailChunk000Sub001Block117Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part005] using hcert

def TailChunk000Sub001Block117Part006SupportExplicit : Finset ℕ :=
  ([13101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part006 : ℚ :=
  (521207011 : ℚ) / 4099362684595200

def SurrogateDiagonalTailChunk000Sub001Block117Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13101
    = surrogateDiagTailX0RatChunk000Sub001Block117Part006

theorem surrogateDiagonalTailChunk000Sub001Block117Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part006] using hcert

def TailChunk000Sub001Block117Part007SupportExplicit : Finset ℕ :=
  ([13102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part007 : ℚ :=
  (42915601 : ℚ) / 73639705246050

def SurrogateDiagonalTailChunk000Sub001Block117Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13102
    = surrogateDiagTailX0RatChunk000Sub001Block117Part007

theorem surrogateDiagonalTailChunk000Sub001Block117Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part007] using hcert

def TailChunk000Sub001Block117Part008SupportExplicit : Finset ℕ :=
  ([13103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block117Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13103
    = surrogateDiagTailX0RatChunk000Sub001Block117Part008

theorem surrogateDiagonalTailChunk000Sub001Block117Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part008] using hcert

def TailChunk000Sub001Block117Part009SupportExplicit : Finset ℕ :=
  ([13105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part009 : ℚ :=
  (34365149149 : ℚ) / 1206512930751283200

def SurrogateDiagonalTailChunk000Sub001Block117Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13105
    = surrogateDiagTailX0RatChunk000Sub001Block117Part009

theorem surrogateDiagonalTailChunk000Sub001Block117Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part009] using hcert

def TailChunk000Sub001Block117Part010SupportExplicit : Finset ℕ :=
  ([13106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part010 : ℚ :=
  (670965765625 : ℚ) / 1152026376153149952

def SurrogateDiagonalTailChunk000Sub001Block117Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13106
    = surrogateDiagTailX0RatChunk000Sub001Block117Part010

theorem surrogateDiagonalTailChunk000Sub001Block117Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part010] using hcert

def TailChunk000Sub001Block117Part011SupportExplicit : Finset ℕ :=
  ([13107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part011 : ℚ :=
  (1206039970225 : ℚ) / 11261250868239925248

def SurrogateDiagonalTailChunk000Sub001Block117Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13107
    = surrogateDiagTailX0RatChunk000Sub001Block117Part011

theorem surrogateDiagonalTailChunk000Sub001Block117Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part011] using hcert

def TailChunk000Sub001Block117Part012SupportExplicit : Finset ℕ :=
  ([13109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block117Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13109
    = surrogateDiagTailX0RatChunk000Sub001Block117Part012

theorem surrogateDiagonalTailChunk000Sub001Block117Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part012] using hcert

def TailChunk000Sub001Block117Part013SupportExplicit : Finset ℕ :=
  ([13110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part013 : ℚ :=
  (49933111775 : ℚ) / 10494368472563712

def SurrogateDiagonalTailChunk000Sub001Block117Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13110
    = surrogateDiagTailX0RatChunk000Sub001Block117Part013

theorem surrogateDiagonalTailChunk000Sub001Block117Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part013] using hcert

def TailChunk000Sub001Block117Part014SupportExplicit : Finset ℕ :=
  ([13111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part014 : ℚ :=
  (12197848075 : ℚ) / 736989801653993472

def SurrogateDiagonalTailChunk000Sub001Block117Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13111
    = surrogateDiagTailX0RatChunk000Sub001Block117Part014

theorem surrogateDiagonalTailChunk000Sub001Block117Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part014] using hcert

def TailChunk000Sub001Block117Part015SupportExplicit : Finset ℕ :=
  ([13114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part015 : ℚ :=
  (200458864825 : ℚ) / 321897294762915456

def SurrogateDiagonalTailChunk000Sub001Block117Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13114
    = surrogateDiagTailX0RatChunk000Sub001Block117Part015

theorem surrogateDiagonalTailChunk000Sub001Block117Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part015] using hcert

def TailChunk000Sub001Block117Part016SupportExplicit : Finset ℕ :=
  ([13115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part016 : ℚ :=
  (12234452053 : ℚ) / 344197509768806400

def SurrogateDiagonalTailChunk000Sub001Block117Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13115
    = surrogateDiagTailX0RatChunk000Sub001Block117Part016

theorem surrogateDiagonalTailChunk000Sub001Block117Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part016] using hcert

def TailChunk000Sub001Block117Part017SupportExplicit : Finset ℕ :=
  ([13117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part017 : ℚ :=
  (35668754125 : ℚ) / 5947732968804974592

def SurrogateDiagonalTailChunk000Sub001Block117Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13117
    = surrogateDiagTailX0RatChunk000Sub001Block117Part017

theorem surrogateDiagonalTailChunk000Sub001Block117Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part017] using hcert

def TailChunk000Sub001Block117Part018SupportExplicit : Finset ℕ :=
  ([13118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part018 : ℚ :=
  (275435241775 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub001Block117Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13118
    = surrogateDiagTailX0RatChunk000Sub001Block117Part018

theorem surrogateDiagonalTailChunk000Sub001Block117Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part018] using hcert

def TailChunk000Sub001Block117Part019SupportExplicit : Finset ℕ :=
  ([13119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part019 : ℚ :=
  (149409259775 : ℚ) / 1827163738172979456

def SurrogateDiagonalTailChunk000Sub001Block117Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13119
    = surrogateDiagTailX0RatChunk000Sub001Block117Part019

theorem surrogateDiagonalTailChunk000Sub001Block117Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part019] using hcert

def TailChunk000Sub001Block117Part020SupportExplicit : Finset ℕ :=
  ([13121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block117Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13121
    = surrogateDiagTailX0RatChunk000Sub001Block117Part020

theorem surrogateDiagonalTailChunk000Sub001Block117Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part020] using hcert

def TailChunk000Sub001Block117Part021SupportExplicit : Finset ℕ :=
  ([13123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part021 : ℚ :=
  (4775068887 : ℚ) / 673086092465766400

def SurrogateDiagonalTailChunk000Sub001Block117Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13123
    = surrogateDiagTailX0RatChunk000Sub001Block117Part021

theorem surrogateDiagonalTailChunk000Sub001Block117Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part021] using hcert

def TailChunk000Sub001Block117Part022SupportExplicit : Finset ℕ :=
  ([13126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block117Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13126
    = surrogateDiagTailX0RatChunk000Sub001Block117Part022

theorem surrogateDiagonalTailChunk000Sub001Block117Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part022] using hcert

def TailChunk000Sub001Block117Part023SupportExplicit : Finset ℕ :=
  ([13127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block117Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13127
    = surrogateDiagTailX0RatChunk000Sub001Block117Part023

theorem surrogateDiagonalTailChunk000Sub001Block117Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part023] using hcert

def TailChunk000Sub001Block117Part024SupportExplicit : Finset ℕ :=
  ([13129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block117Part024 : ℚ :=
  (949626653 : ℚ) / 264442177203868800

def SurrogateDiagonalTailChunk000Sub001Block117Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13129
    = surrogateDiagTailX0RatChunk000Sub001Block117Part024

theorem surrogateDiagonalTailChunk000Sub001Block117Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block117Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block117Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block117Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block117Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block117Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block117Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block117HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block117Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block117Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block117Part000
    + surrogateDiagTailX0RatChunk000Sub001Block117Part001
    + surrogateDiagTailX0RatChunk000Sub001Block117Part002
    + surrogateDiagTailX0RatChunk000Sub001Block117Part003
    + surrogateDiagTailX0RatChunk000Sub001Block117Part004
    + surrogateDiagTailX0RatChunk000Sub001Block117Part005
    + surrogateDiagTailX0RatChunk000Sub001Block117Part006
    + surrogateDiagTailX0RatChunk000Sub001Block117Part007
    + surrogateDiagTailX0RatChunk000Sub001Block117Part008
    + surrogateDiagTailX0RatChunk000Sub001Block117Part009

def surrogateDiagonalTailChunk000Sub001Block117MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block117Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block117Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block117Part010
    + surrogateDiagTailX0RatChunk000Sub001Block117Part011
    + surrogateDiagTailX0RatChunk000Sub001Block117Part012
    + surrogateDiagTailX0RatChunk000Sub001Block117Part013
    + surrogateDiagTailX0RatChunk000Sub001Block117Part014
    + surrogateDiagTailX0RatChunk000Sub001Block117Part015
    + surrogateDiagTailX0RatChunk000Sub001Block117Part016
    + surrogateDiagTailX0RatChunk000Sub001Block117Part017
    + surrogateDiagTailX0RatChunk000Sub001Block117Part018
    + surrogateDiagTailX0RatChunk000Sub001Block117Part019

def surrogateDiagonalTailChunk000Sub001Block117TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block117Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block117Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block117Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block117Part020
    + surrogateDiagTailX0RatChunk000Sub001Block117Part021
    + surrogateDiagTailX0RatChunk000Sub001Block117Part022
    + surrogateDiagTailX0RatChunk000Sub001Block117Part023
    + surrogateDiagTailX0RatChunk000Sub001Block117Part024

def surrogateDiagonalTailChunk000Sub001Block117Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block117HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block117MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block117TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block117 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block117Part000
    + surrogateDiagTailX0RatChunk000Sub001Block117Part001
    + surrogateDiagTailX0RatChunk000Sub001Block117Part002
    + surrogateDiagTailX0RatChunk000Sub001Block117Part003
    + surrogateDiagTailX0RatChunk000Sub001Block117Part004
    + surrogateDiagTailX0RatChunk000Sub001Block117Part005
    + surrogateDiagTailX0RatChunk000Sub001Block117Part006
    + surrogateDiagTailX0RatChunk000Sub001Block117Part007
    + surrogateDiagTailX0RatChunk000Sub001Block117Part008
    + surrogateDiagTailX0RatChunk000Sub001Block117Part009
    + surrogateDiagTailX0RatChunk000Sub001Block117Part010
    + surrogateDiagTailX0RatChunk000Sub001Block117Part011
    + surrogateDiagTailX0RatChunk000Sub001Block117Part012
    + surrogateDiagTailX0RatChunk000Sub001Block117Part013
    + surrogateDiagTailX0RatChunk000Sub001Block117Part014
    + surrogateDiagTailX0RatChunk000Sub001Block117Part015
    + surrogateDiagTailX0RatChunk000Sub001Block117Part016
    + surrogateDiagTailX0RatChunk000Sub001Block117Part017
    + surrogateDiagTailX0RatChunk000Sub001Block117Part018
    + surrogateDiagTailX0RatChunk000Sub001Block117Part019
    + surrogateDiagTailX0RatChunk000Sub001Block117Part020
    + surrogateDiagTailX0RatChunk000Sub001Block117Part021
    + surrogateDiagTailX0RatChunk000Sub001Block117Part022
    + surrogateDiagTailX0RatChunk000Sub001Block117Part023
    + surrogateDiagTailX0RatChunk000Sub001Block117Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block117_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block117Head + surrogateDiagTailX0RatChunk000Sub001Block117Mid + surrogateDiagTailX0RatChunk000Sub001Block117Tail =
      surrogateDiagTailX0RatChunk000Sub001Block117 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block117Head surrogateDiagTailX0RatChunk000Sub001Block117Mid surrogateDiagTailX0RatChunk000Sub001Block117Tail surrogateDiagTailX0RatChunk000Sub001Block117
  ring

def SurrogateDiagonalTailChunk000Sub001Block117HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block117HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block117Head

def SurrogateDiagonalTailChunk000Sub001Block117MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block117MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block117Mid

def SurrogateDiagonalTailChunk000Sub001Block117TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block117TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block117Tail

theorem surrogateDiagonalTailChunk000Sub001Block117_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block117HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block117MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block117TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block117Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block117 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block117HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block117MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block117TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block117Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block117_eq_head_add_mid_add_tail

/-- Block 118 covers tail-support indices [7950,7975) and q from 13130 to 13169. -/

def TailChunk000Sub001Block118Part000SupportExplicit : Finset ℕ :=
  ([13130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part000 : ℚ :=
  (994443449 : ℚ) / 2654738841600000

def SurrogateDiagonalTailChunk000Sub001Block118Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13130
    = surrogateDiagTailX0RatChunk000Sub001Block118Part000

theorem surrogateDiagonalTailChunk000Sub001Block118Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part000] using hcert

def TailChunk000Sub001Block118Part001SupportExplicit : Finset ℕ :=
  ([13133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part001 : ℚ :=
  (7573121131 : ℚ) / 2473301131570051200

def SurrogateDiagonalTailChunk000Sub001Block118Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13133
    = surrogateDiagTailX0RatChunk000Sub001Block118Part001

theorem surrogateDiagonalTailChunk000Sub001Block118Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part001] using hcert

def TailChunk000Sub001Block118Part002SupportExplicit : Finset ℕ :=
  ([13134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part002 : ℚ :=
  (764201363 : ℚ) / 768630503361600

def SurrogateDiagonalTailChunk000Sub001Block118Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13134
    = surrogateDiagTailX0RatChunk000Sub001Block118Part002

theorem surrogateDiagonalTailChunk000Sub001Block118Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part002] using hcert

def TailChunk000Sub001Block118Part003SupportExplicit : Finset ℕ :=
  ([13135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part003 : ℚ :=
  (152025611 : ℚ) / 4249351972454400

def SurrogateDiagonalTailChunk000Sub001Block118Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13135
    = surrogateDiagTailX0RatChunk000Sub001Block118Part003

theorem surrogateDiagonalTailChunk000Sub001Block118Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part003] using hcert

def TailChunk000Sub001Block118Part004SupportExplicit : Finset ℕ :=
  ([13137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part004 : ℚ :=
  (5383420429 : ℚ) / 55330103808000000

def SurrogateDiagonalTailChunk000Sub001Block118Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13137
    = surrogateDiagTailX0RatChunk000Sub001Block118Part004

theorem surrogateDiagonalTailChunk000Sub001Block118Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part004] using hcert

def TailChunk000Sub001Block118Part005SupportExplicit : Finset ℕ :=
  ([13138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block118Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13138
    = surrogateDiagTailX0RatChunk000Sub001Block118Part005

theorem surrogateDiagonalTailChunk000Sub001Block118Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part005] using hcert

def TailChunk000Sub001Block118Part006SupportExplicit : Finset ℕ :=
  ([13139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part006 : ℚ :=
  (749992825 : ℚ) / 45508719052145664

def SurrogateDiagonalTailChunk000Sub001Block118Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13139
    = surrogateDiagTailX0RatChunk000Sub001Block118Part006

theorem surrogateDiagonalTailChunk000Sub001Block118Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part006] using hcert

def TailChunk000Sub001Block118Part007SupportExplicit : Finset ℕ :=
  ([13141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part007 : ℚ :=
  (132714158675 : ℚ) / 29103551909204066304

def SurrogateDiagonalTailChunk000Sub001Block118Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13141
    = surrogateDiagTailX0RatChunk000Sub001Block118Part007

theorem surrogateDiagonalTailChunk000Sub001Block118Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part007] using hcert

def TailChunk000Sub001Block118Part008SupportExplicit : Finset ℕ :=
  ([13142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block118Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13142
    = surrogateDiagTailX0RatChunk000Sub001Block118Part008

theorem surrogateDiagonalTailChunk000Sub001Block118Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part008] using hcert

def TailChunk000Sub001Block118Part009SupportExplicit : Finset ℕ :=
  ([13143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part009 : ℚ :=
  (22744118375 : ℚ) / 195810138890698752

def SurrogateDiagonalTailChunk000Sub001Block118Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13143
    = surrogateDiagTailX0RatChunk000Sub001Block118Part009

theorem surrogateDiagonalTailChunk000Sub001Block118Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part009] using hcert

def TailChunk000Sub001Block118Part010SupportExplicit : Finset ℕ :=
  ([13145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part010 : ℚ :=
  (39861546217 : ℚ) / 821551217804083200

def SurrogateDiagonalTailChunk000Sub001Block118Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13145
    = surrogateDiagTailX0RatChunk000Sub001Block118Part010

theorem surrogateDiagonalTailChunk000Sub001Block118Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part010] using hcert

def TailChunk000Sub001Block118Part011SupportExplicit : Finset ℕ :=
  ([13146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part011 : ℚ :=
  (154535812075 : ℚ) / 122831633608998912

def SurrogateDiagonalTailChunk000Sub001Block118Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13146
    = surrogateDiagTailX0RatChunk000Sub001Block118Part011

theorem surrogateDiagonalTailChunk000Sub001Block118Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part011] using hcert

def TailChunk000Sub001Block118Part012SupportExplicit : Finset ℕ :=
  ([13147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block118Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13147
    = surrogateDiagTailX0RatChunk000Sub001Block118Part012

theorem surrogateDiagonalTailChunk000Sub001Block118Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part012] using hcert

def TailChunk000Sub001Block118Part013SupportExplicit : Finset ℕ :=
  ([13151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block118Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13151
    = surrogateDiagTailX0RatChunk000Sub001Block118Part013

theorem surrogateDiagonalTailChunk000Sub001Block118Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part013] using hcert

def TailChunk000Sub001Block118Part014SupportExplicit : Finset ℕ :=
  ([13153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part014 : ℚ :=
  (221323554575 : ℚ) / 20155065621201543744

def SurrogateDiagonalTailChunk000Sub001Block118Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13153
    = surrogateDiagTailX0RatChunk000Sub001Block118Part014

theorem surrogateDiagonalTailChunk000Sub001Block118Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part014] using hcert

def TailChunk000Sub001Block118Part015SupportExplicit : Finset ℕ :=
  ([13154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block118Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13154
    = surrogateDiagTailX0RatChunk000Sub001Block118Part015

theorem surrogateDiagonalTailChunk000Sub001Block118Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part015] using hcert

def TailChunk000Sub001Block118Part016SupportExplicit : Finset ℕ :=
  ([13155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part016 : ℚ :=
  (1105736937325 : ℚ) / 6031193073265410048

def SurrogateDiagonalTailChunk000Sub001Block118Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13155
    = surrogateDiagTailX0RatChunk000Sub001Block118Part016

theorem surrogateDiagonalTailChunk000Sub001Block118Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part016] using hcert

def TailChunk000Sub001Block118Part017SupportExplicit : Finset ℕ :=
  ([13157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part017 : ℚ :=
  (28552411175 : ℚ) / 22910231426703808896

def SurrogateDiagonalTailChunk000Sub001Block118Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13157
    = surrogateDiagTailX0RatChunk000Sub001Block118Part017

theorem surrogateDiagonalTailChunk000Sub001Block118Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part017] using hcert

def TailChunk000Sub001Block118Part018SupportExplicit : Finset ℕ :=
  ([13159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part018 : ℚ :=
  (2705613765625 : ℚ) / 18738136392543738162

def SurrogateDiagonalTailChunk000Sub001Block118Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13159
    = surrogateDiagTailX0RatChunk000Sub001Block118Part018

theorem surrogateDiagonalTailChunk000Sub001Block118Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part018] using hcert

def TailChunk000Sub001Block118Part019SupportExplicit : Finset ℕ :=
  ([13161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part019 : ℚ :=
  (76085468511 : ℚ) / 172404661642854400

def SurrogateDiagonalTailChunk000Sub001Block118Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13161
    = surrogateDiagTailX0RatChunk000Sub001Block118Part019

theorem surrogateDiagonalTailChunk000Sub001Block118Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part019] using hcert

def TailChunk000Sub001Block118Part020SupportExplicit : Finset ℕ :=
  ([13162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part020 : ℚ :=
  (1082739025 : ℚ) / 1874953168610592

def SurrogateDiagonalTailChunk000Sub001Block118Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13162
    = surrogateDiagTailX0RatChunk000Sub001Block118Part020

theorem surrogateDiagonalTailChunk000Sub001Block118Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part020] using hcert

def TailChunk000Sub001Block118Part021SupportExplicit : Finset ℕ :=
  ([13163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part021 : ℚ :=
  (2707258890625 : ℚ) / 18760932176275235442

def SurrogateDiagonalTailChunk000Sub001Block118Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13163
    = surrogateDiagTailX0RatChunk000Sub001Block118Part021

theorem surrogateDiagonalTailChunk000Sub001Block118Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part021] using hcert

def TailChunk000Sub001Block118Part022SupportExplicit : Finset ℕ :=
  ([13165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part022 : ℚ :=
  (7362331127275 : ℚ) / 30719232714515939328

def SurrogateDiagonalTailChunk000Sub001Block118Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13165
    = surrogateDiagTailX0RatChunk000Sub001Block118Part022

theorem surrogateDiagonalTailChunk000Sub001Block118Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part022] using hcert

def TailChunk000Sub001Block118Part023SupportExplicit : Finset ℕ :=
  ([13166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part023 : ℚ :=
  (214910363175 : ℚ) / 334126941101868544

def SurrogateDiagonalTailChunk000Sub001Block118Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13166
    = surrogateDiagTailX0RatChunk000Sub001Block118Part023

theorem surrogateDiagonalTailChunk000Sub001Block118Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part023] using hcert

def TailChunk000Sub001Block118Part024SupportExplicit : Finset ℕ :=
  ([13169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block118Part024 : ℚ :=
  (1579691923375 : ℚ) / 9064057307810807808

def SurrogateDiagonalTailChunk000Sub001Block118Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13169
    = surrogateDiagTailX0RatChunk000Sub001Block118Part024

theorem surrogateDiagonalTailChunk000Sub001Block118Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block118Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block118Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block118Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block118Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block118Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block118Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block118HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block118Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block118Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block118Part000
    + surrogateDiagTailX0RatChunk000Sub001Block118Part001
    + surrogateDiagTailX0RatChunk000Sub001Block118Part002
    + surrogateDiagTailX0RatChunk000Sub001Block118Part003
    + surrogateDiagTailX0RatChunk000Sub001Block118Part004
    + surrogateDiagTailX0RatChunk000Sub001Block118Part005
    + surrogateDiagTailX0RatChunk000Sub001Block118Part006
    + surrogateDiagTailX0RatChunk000Sub001Block118Part007
    + surrogateDiagTailX0RatChunk000Sub001Block118Part008
    + surrogateDiagTailX0RatChunk000Sub001Block118Part009

def surrogateDiagonalTailChunk000Sub001Block118MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block118Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block118Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block118Part010
    + surrogateDiagTailX0RatChunk000Sub001Block118Part011
    + surrogateDiagTailX0RatChunk000Sub001Block118Part012
    + surrogateDiagTailX0RatChunk000Sub001Block118Part013
    + surrogateDiagTailX0RatChunk000Sub001Block118Part014
    + surrogateDiagTailX0RatChunk000Sub001Block118Part015
    + surrogateDiagTailX0RatChunk000Sub001Block118Part016
    + surrogateDiagTailX0RatChunk000Sub001Block118Part017
    + surrogateDiagTailX0RatChunk000Sub001Block118Part018
    + surrogateDiagTailX0RatChunk000Sub001Block118Part019

def surrogateDiagonalTailChunk000Sub001Block118TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block118Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block118Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block118Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block118Part020
    + surrogateDiagTailX0RatChunk000Sub001Block118Part021
    + surrogateDiagTailX0RatChunk000Sub001Block118Part022
    + surrogateDiagTailX0RatChunk000Sub001Block118Part023
    + surrogateDiagTailX0RatChunk000Sub001Block118Part024

def surrogateDiagonalTailChunk000Sub001Block118Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block118HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block118MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block118TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block118 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block118Part000
    + surrogateDiagTailX0RatChunk000Sub001Block118Part001
    + surrogateDiagTailX0RatChunk000Sub001Block118Part002
    + surrogateDiagTailX0RatChunk000Sub001Block118Part003
    + surrogateDiagTailX0RatChunk000Sub001Block118Part004
    + surrogateDiagTailX0RatChunk000Sub001Block118Part005
    + surrogateDiagTailX0RatChunk000Sub001Block118Part006
    + surrogateDiagTailX0RatChunk000Sub001Block118Part007
    + surrogateDiagTailX0RatChunk000Sub001Block118Part008
    + surrogateDiagTailX0RatChunk000Sub001Block118Part009
    + surrogateDiagTailX0RatChunk000Sub001Block118Part010
    + surrogateDiagTailX0RatChunk000Sub001Block118Part011
    + surrogateDiagTailX0RatChunk000Sub001Block118Part012
    + surrogateDiagTailX0RatChunk000Sub001Block118Part013
    + surrogateDiagTailX0RatChunk000Sub001Block118Part014
    + surrogateDiagTailX0RatChunk000Sub001Block118Part015
    + surrogateDiagTailX0RatChunk000Sub001Block118Part016
    + surrogateDiagTailX0RatChunk000Sub001Block118Part017
    + surrogateDiagTailX0RatChunk000Sub001Block118Part018
    + surrogateDiagTailX0RatChunk000Sub001Block118Part019
    + surrogateDiagTailX0RatChunk000Sub001Block118Part020
    + surrogateDiagTailX0RatChunk000Sub001Block118Part021
    + surrogateDiagTailX0RatChunk000Sub001Block118Part022
    + surrogateDiagTailX0RatChunk000Sub001Block118Part023
    + surrogateDiagTailX0RatChunk000Sub001Block118Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block118_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block118Head + surrogateDiagTailX0RatChunk000Sub001Block118Mid + surrogateDiagTailX0RatChunk000Sub001Block118Tail =
      surrogateDiagTailX0RatChunk000Sub001Block118 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block118Head surrogateDiagTailX0RatChunk000Sub001Block118Mid surrogateDiagTailX0RatChunk000Sub001Block118Tail surrogateDiagTailX0RatChunk000Sub001Block118
  ring

def SurrogateDiagonalTailChunk000Sub001Block118HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block118HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block118Head

def SurrogateDiagonalTailChunk000Sub001Block118MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block118MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block118Mid

def SurrogateDiagonalTailChunk000Sub001Block118TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block118TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block118Tail

theorem surrogateDiagonalTailChunk000Sub001Block118_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block118HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block118MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block118TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block118Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block118 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block118HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block118MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block118TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block118Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block118_eq_head_add_mid_add_tail

/-- Block 119 covers tail-support indices [7975,8000) and q from 13170 to 13211. -/

def TailChunk000Sub001Block119Part000SupportExplicit : Finset ℕ :=
  ([13170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part000 : ℚ :=
  (684827687525 : ℚ) / 188474783539544064

def SurrogateDiagonalTailChunk000Sub001Block119Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13170
    = surrogateDiagTailX0RatChunk000Sub001Block119Part000

theorem surrogateDiagonalTailChunk000Sub001Block119Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part000] using hcert

def TailChunk000Sub001Block119Part001SupportExplicit : Finset ℕ :=
  ([13171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part001 : ℚ :=
  (4336881025 : ℚ) / 30090537815392242

def SurrogateDiagonalTailChunk000Sub001Block119Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13171
    = surrogateDiagTailX0RatChunk000Sub001Block119Part001

theorem surrogateDiagonalTailChunk000Sub001Block119Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part001] using hcert

def TailChunk000Sub001Block119Part002SupportExplicit : Finset ℕ :=
  ([13173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part002 : ℚ :=
  (60241196827 : ℚ) / 148595248471072800

def SurrogateDiagonalTailChunk000Sub001Block119Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13173
    = surrogateDiagTailX0RatChunk000Sub001Block119Part002

theorem surrogateDiagonalTailChunk000Sub001Block119Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part002] using hcert

def TailChunk000Sub001Block119Part003SupportExplicit : Finset ℕ :=
  ([13174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part003 : ℚ :=
  (88450787863 : ℚ) / 101205302229043200

def SurrogateDiagonalTailChunk000Sub001Block119Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13174
    = surrogateDiagTailX0RatChunk000Sub001Block119Part003

theorem surrogateDiagonalTailChunk000Sub001Block119Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part003] using hcert

def TailChunk000Sub001Block119Part004SupportExplicit : Finset ℕ :=
  ([13177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part004 : ℚ :=
  (2713020765625 : ℚ) / 18840881245179843072

def SurrogateDiagonalTailChunk000Sub001Block119Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13177
    = surrogateDiagTailX0RatChunk000Sub001Block119Part004

theorem surrogateDiagonalTailChunk000Sub001Block119Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part004] using hcert

def TailChunk000Sub001Block119Part005SupportExplicit : Finset ℕ :=
  ([13178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part005 : ℚ :=
  (1401399243 : ℚ) / 1853712999132800

def SurrogateDiagonalTailChunk000Sub001Block119Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13178
    = surrogateDiagTailX0RatChunk000Sub001Block119Part005

theorem surrogateDiagonalTailChunk000Sub001Block119Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part005] using hcert

def TailChunk000Sub001Block119Part006SupportExplicit : Finset ℕ :=
  ([13179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part006 : ℚ :=
  (89843971433 : ℚ) / 244276654969881600

def SurrogateDiagonalTailChunk000Sub001Block119Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13179
    = surrogateDiagTailX0RatChunk000Sub001Block119Part006

theorem surrogateDiagonalTailChunk000Sub001Block119Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part006] using hcert

def TailChunk000Sub001Block119Part007SupportExplicit : Finset ℕ :=
  ([13183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part007 : ℚ :=
  (2715492015625 : ℚ) / 18875223238999451922

def SurrogateDiagonalTailChunk000Sub001Block119Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13183
    = surrogateDiagTailX0RatChunk000Sub001Block119Part007

theorem surrogateDiagonalTailChunk000Sub001Block119Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part007] using hcert

def TailChunk000Sub001Block119Part008SupportExplicit : Finset ℕ :=
  ([13186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part008 : ℚ :=
  (422513991575 : ℚ) / 627003585135338688

def SurrogateDiagonalTailChunk000Sub001Block119Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13186
    = surrogateDiagTailX0RatChunk000Sub001Block119Part008

theorem surrogateDiagonalTailChunk000Sub001Block119Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part008] using hcert

def TailChunk000Sub001Block119Part009SupportExplicit : Finset ℕ :=
  ([13187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part009 : ℚ :=
  (2717140140625 : ℚ) / 18898143968891184402

def SurrogateDiagonalTailChunk000Sub001Block119Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13187
    = surrogateDiagTailX0RatChunk000Sub001Block119Part009

theorem surrogateDiagonalTailChunk000Sub001Block119Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part009] using hcert

def TailChunk000Sub001Block119Part010SupportExplicit : Finset ℕ :=
  ([13190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part010 : ℚ :=
  (651939584475 : ℚ) / 643883373084645376

def SurrogateDiagonalTailChunk000Sub001Block119Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13190
    = surrogateDiagTailX0RatChunk000Sub001Block119Part010

theorem surrogateDiagonalTailChunk000Sub001Block119Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part010] using hcert

def TailChunk000Sub001Block119Part011SupportExplicit : Finset ℕ :=
  ([13191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part011 : ℚ :=
  (4831828560325 : ℚ) / 14940928125461710848

def SurrogateDiagonalTailChunk000Sub001Block119Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13191
    = surrogateDiagTailX0RatChunk000Sub001Block119Part011

theorem surrogateDiagonalTailChunk000Sub001Block119Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part011] using hcert

def TailChunk000Sub001Block119Part012SupportExplicit : Finset ℕ :=
  ([13193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part012 : ℚ :=
  (10551507881425 : ℚ) / 70280949758514887808

def SurrogateDiagonalTailChunk000Sub001Block119Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13193
    = surrogateDiagTailX0RatChunk000Sub001Block119Part012

theorem surrogateDiagonalTailChunk000Sub001Block119Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part012] using hcert

def TailChunk000Sub001Block119Part013SupportExplicit : Finset ℕ :=
  ([13195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part013 : ℚ :=
  (22026763925 : ℚ) / 48952534722674688

def SurrogateDiagonalTailChunk000Sub001Block119Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13195
    = surrogateDiagTailX0RatChunk000Sub001Block119Part013

theorem surrogateDiagonalTailChunk000Sub001Block119Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part013] using hcert

def TailChunk000Sub001Block119Part014SupportExplicit : Finset ℕ :=
  ([13197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part014 : ℚ :=
  (1542117092025 : ℚ) / 4408535790004043776

def SurrogateDiagonalTailChunk000Sub001Block119Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13197
    = surrogateDiagTailX0RatChunk000Sub001Block119Part014

theorem surrogateDiagonalTailChunk000Sub001Block119Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part014] using hcert

def TailChunk000Sub001Block119Part015SupportExplicit : Finset ℕ :=
  ([13198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part015 : ℚ :=
  (680418765625 : ℚ) / 1184721070102663602

def SurrogateDiagonalTailChunk000Sub001Block119Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13198
    = surrogateDiagTailX0RatChunk000Sub001Block119Part015

theorem surrogateDiagonalTailChunk000Sub001Block119Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part015] using hcert

def TailChunk000Sub001Block119Part016SupportExplicit : Finset ℕ :=
  ([13199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part016 : ℚ :=
  (167271261275 : ℚ) / 1111440804398217216

def SurrogateDiagonalTailChunk000Sub001Block119Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13199
    = surrogateDiagTailX0RatChunk000Sub001Block119Part016

theorem surrogateDiagonalTailChunk000Sub001Block119Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part016] using hcert

def TailChunk000Sub001Block119Part017SupportExplicit : Finset ℕ :=
  ([13201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part017 : ℚ :=
  (72399154675 : ℚ) / 473747830665169032

def SurrogateDiagonalTailChunk000Sub001Block119Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13201
    = surrogateDiagTailX0RatChunk000Sub001Block119Part017

theorem surrogateDiagonalTailChunk000Sub001Block119Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part017] using hcert

def TailChunk000Sub001Block119Part018SupportExplicit : Finset ℕ :=
  ([13202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part018 : ℚ :=
  (5109961687 : ℚ) / 4858503922483200

def SurrogateDiagonalTailChunk000Sub001Block119Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13202
    = surrogateDiagTailX0RatChunk000Sub001Block119Part018

theorem surrogateDiagonalTailChunk000Sub001Block119Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part018] using hcert

def TailChunk000Sub001Block119Part019SupportExplicit : Finset ℕ :=
  ([13205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part019 : ℚ :=
  (1681490715475 : ℚ) / 6092747762777137152

def SurrogateDiagonalTailChunk000Sub001Block119Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13205
    = surrogateDiagTailX0RatChunk000Sub001Block119Part019

theorem surrogateDiagonalTailChunk000Sub001Block119Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part019] using hcert

def TailChunk000Sub001Block119Part020SupportExplicit : Finset ℕ :=
  ([13206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part020 : ℚ :=
  (2396452193 : ℚ) / 1296799308000000

def SurrogateDiagonalTailChunk000Sub001Block119Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13206
    = surrogateDiagTailX0RatChunk000Sub001Block119Part020

theorem surrogateDiagonalTailChunk000Sub001Block119Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part020] using hcert

def TailChunk000Sub001Block119Part021SupportExplicit : Finset ℕ :=
  ([13207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part021 : ℚ :=
  (418686014017 : ℚ) / 2752645614175027200

def SurrogateDiagonalTailChunk000Sub001Block119Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13207
    = surrogateDiagTailX0RatChunk000Sub001Block119Part021

theorem surrogateDiagonalTailChunk000Sub001Block119Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part021] using hcert

def TailChunk000Sub001Block119Part022SupportExplicit : Finset ℕ :=
  ([13209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part022 : ℚ :=
  (1142257398025 : ℚ) / 1902481849247072256

def SurrogateDiagonalTailChunk000Sub001Block119Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13209
    = surrogateDiagTailX0RatChunk000Sub001Block119Part022

theorem surrogateDiagonalTailChunk000Sub001Block119Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part022] using hcert

def TailChunk000Sub001Block119Part023SupportExplicit : Finset ℕ :=
  ([13210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part023 : ℚ :=
  (13804948009 : ℚ) / 12956010459955200

def SurrogateDiagonalTailChunk000Sub001Block119Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13210
    = surrogateDiagTailX0RatChunk000Sub001Block119Part023

theorem surrogateDiagonalTailChunk000Sub001Block119Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part023] using hcert

def TailChunk000Sub001Block119Part024SupportExplicit : Finset ℕ :=
  ([13211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block119Part024 : ℚ :=
  (123654579089 : ℚ) / 691338240000000000

def SurrogateDiagonalTailChunk000Sub001Block119Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13211
    = surrogateDiagTailX0RatChunk000Sub001Block119Part024

theorem surrogateDiagonalTailChunk000Sub001Block119Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block119Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block119Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block119Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block119Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block119Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block119Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block119HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block119Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block119Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block119Part000
    + surrogateDiagTailX0RatChunk000Sub001Block119Part001
    + surrogateDiagTailX0RatChunk000Sub001Block119Part002
    + surrogateDiagTailX0RatChunk000Sub001Block119Part003
    + surrogateDiagTailX0RatChunk000Sub001Block119Part004
    + surrogateDiagTailX0RatChunk000Sub001Block119Part005
    + surrogateDiagTailX0RatChunk000Sub001Block119Part006
    + surrogateDiagTailX0RatChunk000Sub001Block119Part007
    + surrogateDiagTailX0RatChunk000Sub001Block119Part008
    + surrogateDiagTailX0RatChunk000Sub001Block119Part009

def surrogateDiagonalTailChunk000Sub001Block119MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block119Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block119Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block119Part010
    + surrogateDiagTailX0RatChunk000Sub001Block119Part011
    + surrogateDiagTailX0RatChunk000Sub001Block119Part012
    + surrogateDiagTailX0RatChunk000Sub001Block119Part013
    + surrogateDiagTailX0RatChunk000Sub001Block119Part014
    + surrogateDiagTailX0RatChunk000Sub001Block119Part015
    + surrogateDiagTailX0RatChunk000Sub001Block119Part016
    + surrogateDiagTailX0RatChunk000Sub001Block119Part017
    + surrogateDiagTailX0RatChunk000Sub001Block119Part018
    + surrogateDiagTailX0RatChunk000Sub001Block119Part019

def surrogateDiagonalTailChunk000Sub001Block119TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block119Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block119Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block119Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block119Part020
    + surrogateDiagTailX0RatChunk000Sub001Block119Part021
    + surrogateDiagTailX0RatChunk000Sub001Block119Part022
    + surrogateDiagTailX0RatChunk000Sub001Block119Part023
    + surrogateDiagTailX0RatChunk000Sub001Block119Part024

def surrogateDiagonalTailChunk000Sub001Block119Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block119HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block119MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block119TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block119 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block119Part000
    + surrogateDiagTailX0RatChunk000Sub001Block119Part001
    + surrogateDiagTailX0RatChunk000Sub001Block119Part002
    + surrogateDiagTailX0RatChunk000Sub001Block119Part003
    + surrogateDiagTailX0RatChunk000Sub001Block119Part004
    + surrogateDiagTailX0RatChunk000Sub001Block119Part005
    + surrogateDiagTailX0RatChunk000Sub001Block119Part006
    + surrogateDiagTailX0RatChunk000Sub001Block119Part007
    + surrogateDiagTailX0RatChunk000Sub001Block119Part008
    + surrogateDiagTailX0RatChunk000Sub001Block119Part009
    + surrogateDiagTailX0RatChunk000Sub001Block119Part010
    + surrogateDiagTailX0RatChunk000Sub001Block119Part011
    + surrogateDiagTailX0RatChunk000Sub001Block119Part012
    + surrogateDiagTailX0RatChunk000Sub001Block119Part013
    + surrogateDiagTailX0RatChunk000Sub001Block119Part014
    + surrogateDiagTailX0RatChunk000Sub001Block119Part015
    + surrogateDiagTailX0RatChunk000Sub001Block119Part016
    + surrogateDiagTailX0RatChunk000Sub001Block119Part017
    + surrogateDiagTailX0RatChunk000Sub001Block119Part018
    + surrogateDiagTailX0RatChunk000Sub001Block119Part019
    + surrogateDiagTailX0RatChunk000Sub001Block119Part020
    + surrogateDiagTailX0RatChunk000Sub001Block119Part021
    + surrogateDiagTailX0RatChunk000Sub001Block119Part022
    + surrogateDiagTailX0RatChunk000Sub001Block119Part023
    + surrogateDiagTailX0RatChunk000Sub001Block119Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block119_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block119Head + surrogateDiagTailX0RatChunk000Sub001Block119Mid + surrogateDiagTailX0RatChunk000Sub001Block119Tail =
      surrogateDiagTailX0RatChunk000Sub001Block119 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block119Head surrogateDiagTailX0RatChunk000Sub001Block119Mid surrogateDiagTailX0RatChunk000Sub001Block119Tail surrogateDiagTailX0RatChunk000Sub001Block119
  ring

def SurrogateDiagonalTailChunk000Sub001Block119HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block119HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block119Head

def SurrogateDiagonalTailChunk000Sub001Block119MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block119MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block119Mid

def SurrogateDiagonalTailChunk000Sub001Block119TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block119TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block119Tail

theorem surrogateDiagonalTailChunk000Sub001Block119_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block119HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block119MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block119TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block119Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block119 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block119HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block119MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block119TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block119Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block119_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
