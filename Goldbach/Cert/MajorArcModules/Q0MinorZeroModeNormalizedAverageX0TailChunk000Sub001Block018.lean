import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [18,19). -/

/-- Block 018 covers tail-support indices [5450,5475) and q from 9013 to 9051. -/

def TailChunk000Sub001Block018Part000SupportExplicit : Finset ℕ :=
  ([9013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part000 : ℚ :=
  (1269283890625 : ℚ) / 4123363286648738592

def SurrogateDiagonalTailChunk000Sub001Block018Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9013
    = surrogateDiagTailX0RatChunk000Sub001Block018Part000

theorem surrogateDiagonalTailChunk000Sub001Block018Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part000] using hcert

def TailChunk000Sub001Block018Part001SupportExplicit : Finset ℕ :=
  ([9014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part001 : ℚ :=
  (2538623298775 : ℚ) / 1030840821662184648

def SurrogateDiagonalTailChunk000Sub001Block018Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9014
    = surrogateDiagTailX0RatChunk000Sub001Block018Part001

theorem surrogateDiagonalTailChunk000Sub001Block018Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part001] using hcert

def TailChunk000Sub001Block018Part002SupportExplicit : Finset ℕ :=
  ([9015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part002 : ℚ :=
  (4656221519 : ℚ) / 2949709824000000

def SurrogateDiagonalTailChunk000Sub001Block018Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9015
    = surrogateDiagTailX0RatChunk000Sub001Block018Part002

theorem surrogateDiagonalTailChunk000Sub001Block018Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part002] using hcert

def TailChunk000Sub001Block018Part003SupportExplicit : Finset ℕ :=
  ([9017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part003 : ℚ :=
  (97657583 : ℚ) / 300241459784700

def SurrogateDiagonalTailChunk000Sub001Block018Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9017
    = surrogateDiagTailX0RatChunk000Sub001Block018Part003

theorem surrogateDiagonalTailChunk000Sub001Block018Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part003] using hcert

def TailChunk000Sub001Block018Part004SupportExplicit : Finset ℕ :=
  ([9019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part004 : ℚ :=
  (2090837723 : ℚ) / 283880626660377600

def SurrogateDiagonalTailChunk000Sub001Block018Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9019
    = surrogateDiagTailX0RatChunk000Sub001Block018Part004

theorem surrogateDiagonalTailChunk000Sub001Block018Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part004] using hcert

def TailChunk000Sub001Block018Part005SupportExplicit : Finset ℕ :=
  ([9021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part005 : ℚ :=
  (2979370583 : ℚ) / 13762166154854400

def SurrogateDiagonalTailChunk000Sub001Block018Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9021
    = surrogateDiagTailX0RatChunk000Sub001Block018Part005

theorem surrogateDiagonalTailChunk000Sub001Block018Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part005] using hcert

def TailChunk000Sub001Block018Part006SupportExplicit : Finset ℕ :=
  ([9022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part006 : ℚ :=
  (1186170222775 : ℚ) / 743115360160401408

def SurrogateDiagonalTailChunk000Sub001Block018Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9022
    = surrogateDiagTailX0RatChunk000Sub001Block018Part006

theorem surrogateDiagonalTailChunk000Sub001Block018Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part006] using hcert

def TailChunk000Sub001Block018Part007SupportExplicit : Finset ℕ :=
  ([9023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part007 : ℚ :=
  (416361591925 : ℚ) / 8918571789927088128

def SurrogateDiagonalTailChunk000Sub001Block018Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9023
    = surrogateDiagTailX0RatChunk000Sub001Block018Part007

theorem surrogateDiagonalTailChunk000Sub001Block018Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part007] using hcert

def TailChunk000Sub001Block018Part008SupportExplicit : Finset ℕ :=
  ([9026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part008 : ℚ :=
  (318237015625 : ℚ) / 259085573706350592

def SurrogateDiagonalTailChunk000Sub001Block018Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9026
    = surrogateDiagTailX0RatChunk000Sub001Block018Part008

theorem surrogateDiagonalTailChunk000Sub001Block018Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part008] using hcert

def TailChunk000Sub001Block018Part009SupportExplicit : Finset ℕ :=
  ([9029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block018Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9029
    = surrogateDiagTailX0RatChunk000Sub001Block018Part009

theorem surrogateDiagonalTailChunk000Sub001Block018Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part009] using hcert

def TailChunk000Sub001Block018Part010SupportExplicit : Finset ℕ :=
  ([9030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part010 : ℚ :=
  (591880201375 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub001Block018Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9030
    = surrogateDiagTailX0RatChunk000Sub001Block018Part010

theorem surrogateDiagonalTailChunk000Sub001Block018Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part010] using hcert

def TailChunk000Sub001Block018Part011SupportExplicit : Finset ℕ :=
  ([9031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part011 : ℚ :=
  (1020098977 : ℚ) / 45221218435200000

def SurrogateDiagonalTailChunk000Sub001Block018Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9031
    = surrogateDiagTailX0RatChunk000Sub001Block018Part011

theorem surrogateDiagonalTailChunk000Sub001Block018Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part011] using hcert

def TailChunk000Sub001Block018Part012SupportExplicit : Finset ℕ :=
  ([9033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part012 : ℚ :=
  (323932207 : ℚ) / 1876613236397760

def SurrogateDiagonalTailChunk000Sub001Block018Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9033
    = surrogateDiagTailX0RatChunk000Sub001Block018Part012

theorem surrogateDiagonalTailChunk000Sub001Block018Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part012] using hcert

def TailChunk000Sub001Block018Part013SupportExplicit : Finset ℕ :=
  ([9034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part013 : ℚ :=
  (318801390625 : ℚ) / 260005539330684192

def SurrogateDiagonalTailChunk000Sub001Block018Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9034
    = surrogateDiagTailX0RatChunk000Sub001Block018Part013

theorem surrogateDiagonalTailChunk000Sub001Block018Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part013] using hcert

def TailChunk000Sub001Block018Part014SupportExplicit : Finset ℕ :=
  ([9035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part014 : ℚ :=
  (693212093275 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk000Sub001Block018Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9035
    = surrogateDiagTailX0RatChunk000Sub001Block018Part014

theorem surrogateDiagonalTailChunk000Sub001Block018Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part014] using hcert

def TailChunk000Sub001Block018Part015SupportExplicit : Finset ℕ :=
  ([9037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part015 : ℚ :=
  (16705992733 : ℚ) / 358963832186755200

def SurrogateDiagonalTailChunk000Sub001Block018Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9037
    = surrogateDiagTailX0RatChunk000Sub001Block018Part015

theorem surrogateDiagonalTailChunk000Sub001Block018Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part015] using hcert

def TailChunk000Sub001Block018Part016SupportExplicit : Finset ℕ :=
  ([9038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part016 : ℚ :=
  (319083765625 : ℚ) / 260466439796995122

def SurrogateDiagonalTailChunk000Sub001Block018Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9038
    = surrogateDiagTailX0RatChunk000Sub001Block018Part016

theorem surrogateDiagonalTailChunk000Sub001Block018Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part016] using hcert

def TailChunk000Sub001Block018Part017SupportExplicit : Finset ℕ :=
  ([9039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part017 : ℚ :=
  (4447767001 : ℚ) / 10707077972997120

def SurrogateDiagonalTailChunk000Sub001Block018Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9039
    = surrogateDiagTailX0RatChunk000Sub001Block018Part017

theorem surrogateDiagonalTailChunk000Sub001Block018Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part017] using hcert

def TailChunk000Sub001Block018Part018SupportExplicit : Finset ℕ :=
  ([9041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block018Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9041
    = surrogateDiagTailX0RatChunk000Sub001Block018Part018

theorem surrogateDiagonalTailChunk000Sub001Block018Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part018] using hcert

def TailChunk000Sub001Block018Part019SupportExplicit : Finset ℕ :=
  ([9042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part019 : ℚ :=
  (178372913 : ℚ) / 27373634912256

def SurrogateDiagonalTailChunk000Sub001Block018Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9042
    = surrogateDiagTailX0RatChunk000Sub001Block018Part019

theorem surrogateDiagonalTailChunk000Sub001Block018Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part019] using hcert

def TailChunk000Sub001Block018Part020SupportExplicit : Finset ℕ :=
  ([9043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block018Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9043
    = surrogateDiagTailX0RatChunk000Sub001Block018Part020

theorem surrogateDiagonalTailChunk000Sub001Block018Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part020] using hcert

def TailChunk000Sub001Block018Part021SupportExplicit : Finset ℕ :=
  ([9046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part021 : ℚ :=
  (319648890625 : ℚ) / 261390078748647282

def SurrogateDiagonalTailChunk000Sub001Block018Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9046
    = surrogateDiagTailX0RatChunk000Sub001Block018Part021

theorem surrogateDiagonalTailChunk000Sub001Block018Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part021] using hcert

def TailChunk000Sub001Block018Part022SupportExplicit : Finset ℕ :=
  ([9047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part022 : ℚ :=
  (58755122875 : ℚ) / 15380742109709518848

def SurrogateDiagonalTailChunk000Sub001Block018Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9047
    = surrogateDiagTailX0RatChunk000Sub001Block018Part022

theorem surrogateDiagonalTailChunk000Sub001Block018Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part022] using hcert

def TailChunk000Sub001Block018Part023SupportExplicit : Finset ℕ :=
  ([9049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block018Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9049
    = surrogateDiagTailX0RatChunk000Sub001Block018Part023

theorem surrogateDiagonalTailChunk000Sub001Block018Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part023] using hcert

def TailChunk000Sub001Block018Part024SupportExplicit : Finset ℕ :=
  ([9051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block018Part024 : ℚ :=
  (266214211 : ℚ) / 437694049305600

def SurrogateDiagonalTailChunk000Sub001Block018Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9051
    = surrogateDiagTailX0RatChunk000Sub001Block018Part024

theorem surrogateDiagonalTailChunk000Sub001Block018Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block018Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block018Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block018Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block018Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block018Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block018HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block018Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block018Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block018Part000
    + surrogateDiagTailX0RatChunk000Sub001Block018Part001
    + surrogateDiagTailX0RatChunk000Sub001Block018Part002
    + surrogateDiagTailX0RatChunk000Sub001Block018Part003
    + surrogateDiagTailX0RatChunk000Sub001Block018Part004
    + surrogateDiagTailX0RatChunk000Sub001Block018Part005
    + surrogateDiagTailX0RatChunk000Sub001Block018Part006
    + surrogateDiagTailX0RatChunk000Sub001Block018Part007
    + surrogateDiagTailX0RatChunk000Sub001Block018Part008
    + surrogateDiagTailX0RatChunk000Sub001Block018Part009

def surrogateDiagonalTailChunk000Sub001Block018MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block018Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block018Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block018Part010
    + surrogateDiagTailX0RatChunk000Sub001Block018Part011
    + surrogateDiagTailX0RatChunk000Sub001Block018Part012
    + surrogateDiagTailX0RatChunk000Sub001Block018Part013
    + surrogateDiagTailX0RatChunk000Sub001Block018Part014
    + surrogateDiagTailX0RatChunk000Sub001Block018Part015
    + surrogateDiagTailX0RatChunk000Sub001Block018Part016
    + surrogateDiagTailX0RatChunk000Sub001Block018Part017
    + surrogateDiagTailX0RatChunk000Sub001Block018Part018
    + surrogateDiagTailX0RatChunk000Sub001Block018Part019

def surrogateDiagonalTailChunk000Sub001Block018TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block018Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block018Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block018Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block018Part020
    + surrogateDiagTailX0RatChunk000Sub001Block018Part021
    + surrogateDiagTailX0RatChunk000Sub001Block018Part022
    + surrogateDiagTailX0RatChunk000Sub001Block018Part023
    + surrogateDiagTailX0RatChunk000Sub001Block018Part024

def surrogateDiagonalTailChunk000Sub001Block018Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block018HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block018MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block018TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block018 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block018Part000
    + surrogateDiagTailX0RatChunk000Sub001Block018Part001
    + surrogateDiagTailX0RatChunk000Sub001Block018Part002
    + surrogateDiagTailX0RatChunk000Sub001Block018Part003
    + surrogateDiagTailX0RatChunk000Sub001Block018Part004
    + surrogateDiagTailX0RatChunk000Sub001Block018Part005
    + surrogateDiagTailX0RatChunk000Sub001Block018Part006
    + surrogateDiagTailX0RatChunk000Sub001Block018Part007
    + surrogateDiagTailX0RatChunk000Sub001Block018Part008
    + surrogateDiagTailX0RatChunk000Sub001Block018Part009
    + surrogateDiagTailX0RatChunk000Sub001Block018Part010
    + surrogateDiagTailX0RatChunk000Sub001Block018Part011
    + surrogateDiagTailX0RatChunk000Sub001Block018Part012
    + surrogateDiagTailX0RatChunk000Sub001Block018Part013
    + surrogateDiagTailX0RatChunk000Sub001Block018Part014
    + surrogateDiagTailX0RatChunk000Sub001Block018Part015
    + surrogateDiagTailX0RatChunk000Sub001Block018Part016
    + surrogateDiagTailX0RatChunk000Sub001Block018Part017
    + surrogateDiagTailX0RatChunk000Sub001Block018Part018
    + surrogateDiagTailX0RatChunk000Sub001Block018Part019
    + surrogateDiagTailX0RatChunk000Sub001Block018Part020
    + surrogateDiagTailX0RatChunk000Sub001Block018Part021
    + surrogateDiagTailX0RatChunk000Sub001Block018Part022
    + surrogateDiagTailX0RatChunk000Sub001Block018Part023
    + surrogateDiagTailX0RatChunk000Sub001Block018Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block018_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block018Head + surrogateDiagTailX0RatChunk000Sub001Block018Mid + surrogateDiagTailX0RatChunk000Sub001Block018Tail =
      surrogateDiagTailX0RatChunk000Sub001Block018 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block018Head surrogateDiagTailX0RatChunk000Sub001Block018Mid surrogateDiagTailX0RatChunk000Sub001Block018Tail surrogateDiagTailX0RatChunk000Sub001Block018
  ring

def SurrogateDiagonalTailChunk000Sub001Block018HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block018HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block018Head

def SurrogateDiagonalTailChunk000Sub001Block018MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block018MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block018Mid

def SurrogateDiagonalTailChunk000Sub001Block018TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block018TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block018Tail

theorem surrogateDiagonalTailChunk000Sub001Block018_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block018HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block018MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block018TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block018Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block018 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block018HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block018MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block018TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block018Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block018_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
