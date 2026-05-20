import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [141,142). -/

/- Block 141 covers tail-support indices [3525,3550) and q from 5854 to 5893. -/

def TailChunk000Sub000Block141Part000SupportExplicit : Finset ℕ :=
  ([5854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part000 : ℚ :=
  (1070701941775 : ℚ) / 183283827682089288

def SurrogateDiagonalTailChunk000Sub000Block141Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5854
    = surrogateDiagTailX0RatChunk000Sub000Block141Part000

theorem surrogateDiagonalTailChunk000Sub000Block141Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part000] using hcert

def TailChunk000Sub000Block141Part001SupportExplicit : Finset ℕ :=
  ([5855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part001 : ℚ :=
  (6850868899 : ℚ) / 4798110687851520

def SurrogateDiagonalTailChunk000Sub000Block141Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5855
    = surrogateDiagTailX0RatChunk000Sub000Block141Part001

theorem surrogateDiagonalTailChunk000Sub000Block141Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part001] using hcert

def TailChunk000Sub000Block141Part002SupportExplicit : Finset ℕ :=
  ([5857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part002 : ℚ :=
  (536007015625 : ℚ) / 735141837946355712

def SurrogateDiagonalTailChunk000Sub000Block141Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5857
    = surrogateDiagTailX0RatChunk000Sub000Block141Part002

theorem surrogateDiagonalTailChunk000Sub000Block141Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part002] using hcert

def TailChunk000Sub000Block141Part003SupportExplicit : Finset ℕ :=
  ([5858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part003 : ℚ :=
  (4075296451 : ℚ) / 614778931200000

def SurrogateDiagonalTailChunk000Sub000Block141Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5858
    = surrogateDiagTailX0RatChunk000Sub000Block141Part003

theorem surrogateDiagonalTailChunk000Sub000Block141Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part003] using hcert

def TailChunk000Sub000Block141Part004SupportExplicit : Finset ℕ :=
  ([5861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part004 : ℚ :=
  (858783025 : ℚ) / 1179443969785632

def SurrogateDiagonalTailChunk000Sub000Block141Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5861
    = surrogateDiagTailX0RatChunk000Sub000Block141Part004

theorem surrogateDiagonalTailChunk000Sub000Block141Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part004] using hcert

def TailChunk000Sub000Block141Part005SupportExplicit : Finset ℕ :=
  ([5862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part005 : ℚ :=
  (655639609975 : ℚ) / 36303300639326208

def SurrogateDiagonalTailChunk000Sub000Block141Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5862
    = surrogateDiagTailX0RatChunk000Sub000Block141Part005

theorem surrogateDiagonalTailChunk000Sub000Block141Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part005] using hcert

def TailChunk000Sub000Block141Part006SupportExplicit : Finset ℕ :=
  ([5863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part006 : ℚ :=
  (6809285131 : ℚ) / 5309477683200000

def SurrogateDiagonalTailChunk000Sub000Block141Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5863
    = surrogateDiagTailX0RatChunk000Sub000Block141Part006

theorem surrogateDiagonalTailChunk000Sub000Block141Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part006] using hcert

def TailChunk000Sub000Block141Part007SupportExplicit : Finset ℕ :=
  ([5865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part007 : ℚ :=
  (488886833075 : ℚ) / 78618990879965184

def SurrogateDiagonalTailChunk000Sub000Block141Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5865
    = surrogateDiagTailX0RatChunk000Sub000Block141Part007

theorem surrogateDiagonalTailChunk000Sub000Block141Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part007] using hcert

def TailChunk000Sub000Block141Part008SupportExplicit : Finset ℕ :=
  ([5866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part008 : ℚ :=
  (448750218725 : ℚ) / 49466022631401024

def SurrogateDiagonalTailChunk000Sub000Block141Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5866
    = surrogateDiagTailX0RatChunk000Sub000Block141Part008

theorem surrogateDiagonalTailChunk000Sub000Block141Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part008] using hcert

def TailChunk000Sub000Block141Part009SupportExplicit : Finset ℕ :=
  ([5867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part009 : ℚ :=
  (537838890625 : ℚ) / 740176175585200242

def SurrogateDiagonalTailChunk000Sub000Block141Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5867
    = surrogateDiagTailX0RatChunk000Sub000Block141Part009

theorem surrogateDiagonalTailChunk000Sub000Block141Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part009] using hcert

def TailChunk000Sub000Block141Part010SupportExplicit : Finset ℕ :=
  ([5869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part010 : ℚ :=
  (538205640625 : ℚ) / 741186137813405472

def SurrogateDiagonalTailChunk000Sub000Block141Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5869
    = surrogateDiagTailX0RatChunk000Sub000Block141Part010

theorem surrogateDiagonalTailChunk000Sub000Block141Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part010] using hcert

def TailChunk000Sub000Block141Part011SupportExplicit : Finset ℕ :=
  ([5870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part011 : ℚ :=
  (419219859575 : ℚ) / 37742207033140224

def SurrogateDiagonalTailChunk000Sub000Block141Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5870
    = surrogateDiagTailX0RatChunk000Sub000Block141Part011

theorem surrogateDiagonalTailChunk000Sub000Block141Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part011] using hcert

def TailChunk000Sub000Block141Part012SupportExplicit : Finset ℕ :=
  ([5871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part012 : ℚ :=
  (667006028525 : ℚ) / 227304248615691264

def SurrogateDiagonalTailChunk000Sub000Block141Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5871
    = surrogateDiagTailX0RatChunk000Sub000Block141Part012

theorem surrogateDiagonalTailChunk000Sub000Block141Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part012] using hcert

def TailChunk000Sub000Block141Part013SupportExplicit : Finset ℕ :=
  ([5873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part013 : ℚ :=
  (3679891925 : ℚ) / 22196036918839824

def SurrogateDiagonalTailChunk000Sub000Block141Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5873
    = surrogateDiagTailX0RatChunk000Sub000Block141Part013

theorem surrogateDiagonalTailChunk000Sub000Block141Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part013] using hcert

def TailChunk000Sub000Block141Part014SupportExplicit : Finset ℕ :=
  ([5874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part014 : ℚ :=
  (8894995847 : ℚ) / 479852239257600

def SurrogateDiagonalTailChunk000Sub000Block141Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5874
    = surrogateDiagTailX0RatChunk000Sub000Block141Part014

theorem surrogateDiagonalTailChunk000Sub000Block141Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part014] using hcert

def TailChunk000Sub000Block141Part015SupportExplicit : Finset ℕ :=
  ([5878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part015 : ℚ :=
  (134964390625 : ℚ) / 46577270366565042

def SurrogateDiagonalTailChunk000Sub000Block141Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5878
    = surrogateDiagTailX0RatChunk000Sub000Block141Part015

theorem surrogateDiagonalTailChunk000Sub000Block141Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part015] using hcert

def TailChunk000Sub000Block141Part016SupportExplicit : Finset ℕ :=
  ([5879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block141Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5879
    = surrogateDiagTailX0RatChunk000Sub000Block141Part016

theorem surrogateDiagonalTailChunk000Sub000Block141Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part016] using hcert

def TailChunk000Sub000Block141Part017SupportExplicit : Finset ℕ :=
  ([5881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block141Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5881
    = surrogateDiagTailX0RatChunk000Sub000Block141Part017

theorem surrogateDiagonalTailChunk000Sub000Block141Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part017] using hcert

def TailChunk000Sub000Block141Part018SupportExplicit : Finset ℕ :=
  ([5882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part018 : ℚ :=
  (176716246725 : ℚ) / 47807862025486336

def SurrogateDiagonalTailChunk000Sub000Block141Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5882
    = surrogateDiagTailX0RatChunk000Sub000Block141Part018

theorem surrogateDiagonalTailChunk000Sub000Block141Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part018] using hcert

def TailChunk000Sub000Block141Part019SupportExplicit : Finset ℕ :=
  ([5883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part019 : ℚ :=
  (1367663130325 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk000Sub000Block141Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5883
    = surrogateDiagTailX0RatChunk000Sub000Block141Part019

theorem surrogateDiagonalTailChunk000Sub000Block141Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part019] using hcert

def TailChunk000Sub000Block141Part020SupportExplicit : Finset ℕ :=
  ([5885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part020 : ℚ :=
  (61237886371 : ℚ) / 32325874058035200

def SurrogateDiagonalTailChunk000Sub000Block141Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5885
    = surrogateDiagTailX0RatChunk000Sub000Block141Part020

theorem surrogateDiagonalTailChunk000Sub000Block141Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part020] using hcert

def TailChunk000Sub000Block141Part021SupportExplicit : Finset ℕ :=
  ([5889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part021 : ℚ :=
  (26141533469 : ℚ) / 8399759616000000

def SurrogateDiagonalTailChunk000Sub000Block141Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5889
    = surrogateDiagTailX0RatChunk000Sub000Block141Part021

theorem surrogateDiagonalTailChunk000Sub000Block141Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part021] using hcert

def TailChunk000Sub000Block141Part022SupportExplicit : Finset ℕ :=
  ([5890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part022 : ℚ :=
  (15342188669 : ℚ) / 1088608846233600

def SurrogateDiagonalTailChunk000Sub000Block141Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5890
    = surrogateDiagTailX0RatChunk000Sub000Block141Part022

theorem surrogateDiagonalTailChunk000Sub000Block141Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part022] using hcert

def TailChunk000Sub000Block141Part023SupportExplicit : Finset ℕ :=
  ([5891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part023 : ℚ :=
  (454492825 : ℚ) / 577653200018496

def SurrogateDiagonalTailChunk000Sub000Block141Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5891
    = surrogateDiagTailX0RatChunk000Sub000Block141Part023

theorem surrogateDiagonalTailChunk000Sub000Block141Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part023] using hcert

def TailChunk000Sub000Block141Part024SupportExplicit : Finset ℕ :=
  ([5893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block141Part024 : ℚ :=
  (3008379217 : ℚ) / 3877719480818400

def SurrogateDiagonalTailChunk000Sub000Block141Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5893
    = surrogateDiagTailX0RatChunk000Sub000Block141Part024

theorem surrogateDiagonalTailChunk000Sub000Block141Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block141Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block141Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block141Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block141Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block141Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block141Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block141HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block141Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block141Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block141Part000
    + surrogateDiagTailX0RatChunk000Sub000Block141Part001
    + surrogateDiagTailX0RatChunk000Sub000Block141Part002
    + surrogateDiagTailX0RatChunk000Sub000Block141Part003
    + surrogateDiagTailX0RatChunk000Sub000Block141Part004
    + surrogateDiagTailX0RatChunk000Sub000Block141Part005
    + surrogateDiagTailX0RatChunk000Sub000Block141Part006
    + surrogateDiagTailX0RatChunk000Sub000Block141Part007
    + surrogateDiagTailX0RatChunk000Sub000Block141Part008
    + surrogateDiagTailX0RatChunk000Sub000Block141Part009

def surrogateDiagonalTailChunk000Sub000Block141MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block141Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block141Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block141Part010
    + surrogateDiagTailX0RatChunk000Sub000Block141Part011
    + surrogateDiagTailX0RatChunk000Sub000Block141Part012
    + surrogateDiagTailX0RatChunk000Sub000Block141Part013
    + surrogateDiagTailX0RatChunk000Sub000Block141Part014
    + surrogateDiagTailX0RatChunk000Sub000Block141Part015
    + surrogateDiagTailX0RatChunk000Sub000Block141Part016
    + surrogateDiagTailX0RatChunk000Sub000Block141Part017
    + surrogateDiagTailX0RatChunk000Sub000Block141Part018
    + surrogateDiagTailX0RatChunk000Sub000Block141Part019

def surrogateDiagonalTailChunk000Sub000Block141TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block141Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block141Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block141Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block141Part020
    + surrogateDiagTailX0RatChunk000Sub000Block141Part021
    + surrogateDiagTailX0RatChunk000Sub000Block141Part022
    + surrogateDiagTailX0RatChunk000Sub000Block141Part023
    + surrogateDiagTailX0RatChunk000Sub000Block141Part024

def surrogateDiagonalTailChunk000Sub000Block141Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block141HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block141MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block141TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block141 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block141Part000
    + surrogateDiagTailX0RatChunk000Sub000Block141Part001
    + surrogateDiagTailX0RatChunk000Sub000Block141Part002
    + surrogateDiagTailX0RatChunk000Sub000Block141Part003
    + surrogateDiagTailX0RatChunk000Sub000Block141Part004
    + surrogateDiagTailX0RatChunk000Sub000Block141Part005
    + surrogateDiagTailX0RatChunk000Sub000Block141Part006
    + surrogateDiagTailX0RatChunk000Sub000Block141Part007
    + surrogateDiagTailX0RatChunk000Sub000Block141Part008
    + surrogateDiagTailX0RatChunk000Sub000Block141Part009
    + surrogateDiagTailX0RatChunk000Sub000Block141Part010
    + surrogateDiagTailX0RatChunk000Sub000Block141Part011
    + surrogateDiagTailX0RatChunk000Sub000Block141Part012
    + surrogateDiagTailX0RatChunk000Sub000Block141Part013
    + surrogateDiagTailX0RatChunk000Sub000Block141Part014
    + surrogateDiagTailX0RatChunk000Sub000Block141Part015
    + surrogateDiagTailX0RatChunk000Sub000Block141Part016
    + surrogateDiagTailX0RatChunk000Sub000Block141Part017
    + surrogateDiagTailX0RatChunk000Sub000Block141Part018
    + surrogateDiagTailX0RatChunk000Sub000Block141Part019
    + surrogateDiagTailX0RatChunk000Sub000Block141Part020
    + surrogateDiagTailX0RatChunk000Sub000Block141Part021
    + surrogateDiagTailX0RatChunk000Sub000Block141Part022
    + surrogateDiagTailX0RatChunk000Sub000Block141Part023
    + surrogateDiagTailX0RatChunk000Sub000Block141Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block141_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block141Head + surrogateDiagTailX0RatChunk000Sub000Block141Mid + surrogateDiagTailX0RatChunk000Sub000Block141Tail =
      surrogateDiagTailX0RatChunk000Sub000Block141 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block141Head surrogateDiagTailX0RatChunk000Sub000Block141Mid surrogateDiagTailX0RatChunk000Sub000Block141Tail surrogateDiagTailX0RatChunk000Sub000Block141
  ring

def SurrogateDiagonalTailChunk000Sub000Block141HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block141HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block141Head

def SurrogateDiagonalTailChunk000Sub000Block141MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block141MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block141Mid

def SurrogateDiagonalTailChunk000Sub000Block141TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block141TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block141Tail

theorem surrogateDiagonalTailChunk000Sub000Block141_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block141HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block141MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block141TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block141Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block141 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block141HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block141MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block141TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block141Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block141_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
