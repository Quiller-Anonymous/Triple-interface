import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [14,15). -/

/-- Block 014 covers tail-support indices [5350,5375) and q from 8843 to 8885. -/

def TailChunk000Sub001Block014Part000SupportExplicit : Finset ℕ :=
  ([8843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part000 : ℚ :=
  (4667312045125 : ℚ) / 13475493850031474688

def SurrogateDiagonalTailChunk000Sub001Block014Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8843
    = surrogateDiagTailX0RatChunk000Sub001Block014Part000

theorem surrogateDiagonalTailChunk000Sub001Block014Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part000] using hcert

def TailChunk000Sub001Block014Part001SupportExplicit : Finset ℕ :=
  ([8845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part001 : ℚ :=
  (131112306961 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block014Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8845
    = surrogateDiagTailX0RatChunk000Sub001Block014Part001

theorem surrogateDiagonalTailChunk000Sub001Block014Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part001] using hcert

def TailChunk000Sub001Block014Part002SupportExplicit : Finset ℕ :=
  ([8846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part002 : ℚ :=
  (305670765625 : ℚ) / 239024170949544882

def SurrogateDiagonalTailChunk000Sub001Block014Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8846
    = surrogateDiagTailX0RatChunk000Sub001Block014Part002

theorem surrogateDiagonalTailChunk000Sub001Block014Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part002] using hcert

def TailChunk000Sub001Block014Part003SupportExplicit : Finset ℕ :=
  ([8849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part003 : ℚ :=
  (1223512515625 : ℚ) / 3831310266773348352

def SurrogateDiagonalTailChunk000Sub001Block014Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8849
    = surrogateDiagTailX0RatChunk000Sub001Block014Part003

theorem surrogateDiagonalTailChunk000Sub001Block014Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part003] using hcert

def TailChunk000Sub001Block014Part004SupportExplicit : Finset ℕ :=
  ([8851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part004 : ℚ :=
  (4722124742125 : ℚ) / 13882656742422693888

def SurrogateDiagonalTailChunk000Sub001Block014Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8851
    = surrogateDiagTailX0RatChunk000Sub001Block014Part004

theorem surrogateDiagonalTailChunk000Sub001Block014Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part004] using hcert

def TailChunk000Sub001Block014Part005SupportExplicit : Finset ℕ :=
  ([8853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part005 : ℚ :=
  (2427534341725 : ℚ) / 2164240811335385088

def SurrogateDiagonalTailChunk000Sub001Block014Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8853
    = surrogateDiagTailX0RatChunk000Sub001Block014Part005

theorem surrogateDiagonalTailChunk000Sub001Block014Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part005] using hcert

def TailChunk000Sub001Block014Part006SupportExplicit : Finset ℕ :=
  ([8854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part006 : ℚ :=
  (751002857875 : ℚ) / 253482256254468096

def SurrogateDiagonalTailChunk000Sub001Block014Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8854
    = surrogateDiagTailX0RatChunk000Sub001Block014Part006

theorem surrogateDiagonalTailChunk000Sub001Block014Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part006] using hcert

def TailChunk000Sub001Block014Part007SupportExplicit : Finset ℕ :=
  ([8855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part007 : ℚ :=
  (94062502351 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk000Sub001Block014Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8855
    = surrogateDiagTailX0RatChunk000Sub001Block014Part007

theorem surrogateDiagonalTailChunk000Sub001Block014Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part007] using hcert

def TailChunk000Sub001Block014Part008SupportExplicit : Finset ℕ :=
  ([8857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part008 : ℚ :=
  (179368471603 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk000Sub001Block014Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8857
    = surrogateDiagTailX0RatChunk000Sub001Block014Part008

theorem surrogateDiagonalTailChunk000Sub001Block014Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part008] using hcert

def TailChunk000Sub001Block014Part009SupportExplicit : Finset ℕ :=
  ([8858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part009 : ℚ :=
  (2337253451725 : ℚ) / 842218365626967168

def SurrogateDiagonalTailChunk000Sub001Block014Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8858
    = surrogateDiagTailX0RatChunk000Sub001Block014Part009

theorem surrogateDiagonalTailChunk000Sub001Block014Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part009] using hcert

def TailChunk000Sub001Block014Part010SupportExplicit : Finset ℕ :=
  ([8859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part010 : ℚ :=
  (1362140289425 : ℚ) / 1519085640465137664

def SurrogateDiagonalTailChunk000Sub001Block014Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8859
    = surrogateDiagTailX0RatChunk000Sub001Block014Part010

theorem surrogateDiagonalTailChunk000Sub001Block014Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part010] using hcert

def TailChunk000Sub001Block014Part011SupportExplicit : Finset ℕ :=
  ([8861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block014Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8861
    = surrogateDiagTailX0RatChunk000Sub001Block014Part011

theorem surrogateDiagonalTailChunk000Sub001Block014Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part011] using hcert

def TailChunk000Sub001Block014Part012SupportExplicit : Finset ℕ :=
  ([8862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part012 : ℚ :=
  (1681 : ℚ) / 237081600

def SurrogateDiagonalTailChunk000Sub001Block014Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8862
    = surrogateDiagTailX0RatChunk000Sub001Block014Part012

theorem surrogateDiagonalTailChunk000Sub001Block014Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part012] using hcert

def TailChunk000Sub001Block014Part013SupportExplicit : Finset ℕ :=
  ([8863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block014Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8863
    = surrogateDiagTailX0RatChunk000Sub001Block014Part013

theorem surrogateDiagonalTailChunk000Sub001Block014Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part013] using hcert

def TailChunk000Sub001Block014Part014SupportExplicit : Finset ℕ :=
  ([8866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part014 : ℚ :=
  (6830392709 : ℚ) / 2799919872000000

def SurrogateDiagonalTailChunk000Sub001Block014Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8866
    = surrogateDiagTailX0RatChunk000Sub001Block014Part014

theorem surrogateDiagonalTailChunk000Sub001Block014Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part014] using hcert

def TailChunk000Sub001Block014Part015SupportExplicit : Finset ℕ :=
  ([8867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block014Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8867
    = surrogateDiagTailX0RatChunk000Sub001Block014Part015

theorem surrogateDiagonalTailChunk000Sub001Block014Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part015] using hcert

def TailChunk000Sub001Block014Part016SupportExplicit : Finset ℕ :=
  ([8870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part016 : ℚ :=
  (343917775125 : ℚ) / 131486285602134016

def SurrogateDiagonalTailChunk000Sub001Block014Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8870
    = surrogateDiagTailX0RatChunk000Sub001Block014Part016

theorem surrogateDiagonalTailChunk000Sub001Block014Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part016] using hcert

def TailChunk000Sub001Block014Part017SupportExplicit : Finset ℕ :=
  ([8871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part017 : ℚ :=
  (8542908025 : ℚ) / 47729247403252512

def SurrogateDiagonalTailChunk000Sub001Block014Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8871
    = surrogateDiagTailX0RatChunk000Sub001Block014Part017

theorem surrogateDiagonalTailChunk000Sub001Block014Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part017] using hcert

def TailChunk000Sub001Block014Part018SupportExplicit : Finset ℕ :=
  ([8873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part018 : ℚ :=
  (51539191525 : ℚ) / 4126095648952246656

def SurrogateDiagonalTailChunk000Sub001Block014Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8873
    = surrogateDiagTailX0RatChunk000Sub001Block014Part018

theorem surrogateDiagonalTailChunk000Sub001Block014Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part018] using hcert

def TailChunk000Sub001Block014Part019SupportExplicit : Finset ℕ :=
  ([8877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part019 : ℚ :=
  (21219480749 : ℚ) / 41277749707161600

def SurrogateDiagonalTailChunk000Sub001Block014Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8877
    = surrogateDiagTailX0RatChunk000Sub001Block014Part019

theorem surrogateDiagonalTailChunk000Sub001Block014Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part019] using hcert

def TailChunk000Sub001Block014Part020SupportExplicit : Finset ℕ :=
  ([8878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part020 : ℚ :=
  (1179799303975 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub001Block014Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8878
    = surrogateDiagTailX0RatChunk000Sub001Block014Part020

theorem surrogateDiagonalTailChunk000Sub001Block014Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part020] using hcert

def TailChunk000Sub001Block014Part021SupportExplicit : Finset ℕ :=
  ([8879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part021 : ℚ :=
  (3136364525 : ℚ) / 169959484886197248

def SurrogateDiagonalTailChunk000Sub001Block014Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8879
    = surrogateDiagTailX0RatChunk000Sub001Block014Part021

theorem surrogateDiagonalTailChunk000Sub001Block014Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part021] using hcert

def TailChunk000Sub001Block014Part022SupportExplicit : Finset ℕ :=
  ([8881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part022 : ℚ :=
  (58224829525 : ℚ) / 14272686594391813248

def SurrogateDiagonalTailChunk000Sub001Block014Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8881
    = surrogateDiagTailX0RatChunk000Sub001Block014Part022

theorem surrogateDiagonalTailChunk000Sub001Block014Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part022] using hcert

def TailChunk000Sub001Block014Part023SupportExplicit : Finset ℕ :=
  ([8882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part023 : ℚ :=
  (493062025 : ℚ) / 388703750164992

def SurrogateDiagonalTailChunk000Sub001Block014Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8882
    = surrogateDiagTailX0RatChunk000Sub001Block014Part023

theorem surrogateDiagonalTailChunk000Sub001Block014Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part023] using hcert

def TailChunk000Sub001Block014Part024SupportExplicit : Finset ℕ :=
  ([8885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block014Part024 : ℚ :=
  (296210783225 : ℚ) / 3184261121351614464

def SurrogateDiagonalTailChunk000Sub001Block014Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8885
    = surrogateDiagTailX0RatChunk000Sub001Block014Part024

theorem surrogateDiagonalTailChunk000Sub001Block014Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block014Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block014Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block014Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block014Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block014Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block014HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block014Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block014Part000
    + surrogateDiagTailX0RatChunk000Sub001Block014Part001
    + surrogateDiagTailX0RatChunk000Sub001Block014Part002
    + surrogateDiagTailX0RatChunk000Sub001Block014Part003
    + surrogateDiagTailX0RatChunk000Sub001Block014Part004
    + surrogateDiagTailX0RatChunk000Sub001Block014Part005
    + surrogateDiagTailX0RatChunk000Sub001Block014Part006
    + surrogateDiagTailX0RatChunk000Sub001Block014Part007
    + surrogateDiagTailX0RatChunk000Sub001Block014Part008
    + surrogateDiagTailX0RatChunk000Sub001Block014Part009

def surrogateDiagonalTailChunk000Sub001Block014MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block014Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block014Part010
    + surrogateDiagTailX0RatChunk000Sub001Block014Part011
    + surrogateDiagTailX0RatChunk000Sub001Block014Part012
    + surrogateDiagTailX0RatChunk000Sub001Block014Part013
    + surrogateDiagTailX0RatChunk000Sub001Block014Part014
    + surrogateDiagTailX0RatChunk000Sub001Block014Part015
    + surrogateDiagTailX0RatChunk000Sub001Block014Part016
    + surrogateDiagTailX0RatChunk000Sub001Block014Part017
    + surrogateDiagTailX0RatChunk000Sub001Block014Part018
    + surrogateDiagTailX0RatChunk000Sub001Block014Part019

def surrogateDiagonalTailChunk000Sub001Block014TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block014Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block014Part020
    + surrogateDiagTailX0RatChunk000Sub001Block014Part021
    + surrogateDiagTailX0RatChunk000Sub001Block014Part022
    + surrogateDiagTailX0RatChunk000Sub001Block014Part023
    + surrogateDiagTailX0RatChunk000Sub001Block014Part024

def surrogateDiagonalTailChunk000Sub001Block014Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block014HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block014MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block014TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block014 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block014Part000
    + surrogateDiagTailX0RatChunk000Sub001Block014Part001
    + surrogateDiagTailX0RatChunk000Sub001Block014Part002
    + surrogateDiagTailX0RatChunk000Sub001Block014Part003
    + surrogateDiagTailX0RatChunk000Sub001Block014Part004
    + surrogateDiagTailX0RatChunk000Sub001Block014Part005
    + surrogateDiagTailX0RatChunk000Sub001Block014Part006
    + surrogateDiagTailX0RatChunk000Sub001Block014Part007
    + surrogateDiagTailX0RatChunk000Sub001Block014Part008
    + surrogateDiagTailX0RatChunk000Sub001Block014Part009
    + surrogateDiagTailX0RatChunk000Sub001Block014Part010
    + surrogateDiagTailX0RatChunk000Sub001Block014Part011
    + surrogateDiagTailX0RatChunk000Sub001Block014Part012
    + surrogateDiagTailX0RatChunk000Sub001Block014Part013
    + surrogateDiagTailX0RatChunk000Sub001Block014Part014
    + surrogateDiagTailX0RatChunk000Sub001Block014Part015
    + surrogateDiagTailX0RatChunk000Sub001Block014Part016
    + surrogateDiagTailX0RatChunk000Sub001Block014Part017
    + surrogateDiagTailX0RatChunk000Sub001Block014Part018
    + surrogateDiagTailX0RatChunk000Sub001Block014Part019
    + surrogateDiagTailX0RatChunk000Sub001Block014Part020
    + surrogateDiagTailX0RatChunk000Sub001Block014Part021
    + surrogateDiagTailX0RatChunk000Sub001Block014Part022
    + surrogateDiagTailX0RatChunk000Sub001Block014Part023
    + surrogateDiagTailX0RatChunk000Sub001Block014Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block014_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block014Head + surrogateDiagTailX0RatChunk000Sub001Block014Mid + surrogateDiagTailX0RatChunk000Sub001Block014Tail =
      surrogateDiagTailX0RatChunk000Sub001Block014 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block014Head surrogateDiagTailX0RatChunk000Sub001Block014Mid surrogateDiagTailX0RatChunk000Sub001Block014Tail surrogateDiagTailX0RatChunk000Sub001Block014
  ring

def SurrogateDiagonalTailChunk000Sub001Block014HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block014HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block014Head

def SurrogateDiagonalTailChunk000Sub001Block014MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block014MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block014Mid

def SurrogateDiagonalTailChunk000Sub001Block014TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block014TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block014Tail

theorem surrogateDiagonalTailChunk000Sub001Block014_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block014HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block014MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block014TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block014Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block014 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block014HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block014MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block014TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block014Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block014_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
