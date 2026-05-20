import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [165,166). -/

/-- Block 165 covers tail-support indices [4125,4150) and q from 6834 to 6874. -/

def TailChunk000Sub000Block165Part000SupportExplicit : Finset ℕ :=
  ([6834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part000 : ℚ :=
  (303071675675 : ℚ) / 24875540083113984

def SurrogateDiagonalTailChunk000Sub000Block165Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6834
    = surrogateDiagTailX0RatChunk000Sub000Block165Part000

theorem surrogateDiagonalTailChunk000Sub000Block165Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part000] using hcert

def TailChunk000Sub000Block165Part001SupportExplicit : Finset ℕ :=
  ([6835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part001 : ℚ :=
  (77909835525 : ℚ) / 371465402911443968

def SurrogateDiagonalTailChunk000Sub000Block165Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6835
    = surrogateDiagTailX0RatChunk000Sub000Block165Part001

theorem surrogateDiagonalTailChunk000Sub000Block165Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part001] using hcert

def TailChunk000Sub000Block165Part002SupportExplicit : Finset ℕ :=
  ([6837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part002 : ℚ :=
  (72690532325 : ℚ) / 101138118071058432

def SurrogateDiagonalTailChunk000Sub000Block165Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6837
    = surrogateDiagTailX0RatChunk000Sub000Block165Part002

theorem surrogateDiagonalTailChunk000Sub000Block165Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part002] using hcert

def TailChunk000Sub000Block165Part003SupportExplicit : Finset ℕ :=
  ([6838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part003 : ℚ :=
  (698872343725 : ℚ) / 244318868477134848

def SurrogateDiagonalTailChunk000Sub000Block165Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6838
    = surrogateDiagTailX0RatChunk000Sub000Block165Part003

theorem surrogateDiagonalTailChunk000Sub000Block165Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part003] using hcert

def TailChunk000Sub000Block165Part004SupportExplicit : Finset ℕ :=
  ([6839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part004 : ℚ :=
  (299316111775 : ℚ) / 2940567351785422848

def SurrogateDiagonalTailChunk000Sub000Block165Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6839
    = surrogateDiagTailX0RatChunk000Sub000Block165Part004

theorem surrogateDiagonalTailChunk000Sub000Block165Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part004] using hcert

def TailChunk000Sub000Block165Part005SupportExplicit : Finset ℕ :=
  ([6841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block165Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6841
    = surrogateDiagTailX0RatChunk000Sub000Block165Part005

theorem surrogateDiagonalTailChunk000Sub000Block165Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part005] using hcert

def TailChunk000Sub000Block165Part006SupportExplicit : Finset ℕ :=
  ([6842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part006 : ℚ :=
  (1110316519 : ℚ) / 369482281680000

def SurrogateDiagonalTailChunk000Sub000Block165Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6842
    = surrogateDiagTailX0RatChunk000Sub000Block165Part006

theorem surrogateDiagonalTailChunk000Sub000Block165Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part006] using hcert

def TailChunk000Sub000Block165Part007SupportExplicit : Finset ℕ :=
  ([6843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part007 : ℚ :=
  (13005898739 : ℚ) / 21623013786009600

def SurrogateDiagonalTailChunk000Sub000Block165Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6843
    = surrogateDiagTailX0RatChunk000Sub000Block165Part007

theorem surrogateDiagonalTailChunk000Sub000Block165Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part007] using hcert

def TailChunk000Sub000Block165Part008SupportExplicit : Finset ℕ :=
  ([6846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part008 : ℚ :=
  (195113975 : ℚ) / 13777705710144

def SurrogateDiagonalTailChunk000Sub000Block165Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6846
    = surrogateDiagTailX0RatChunk000Sub000Block165Part008

theorem surrogateDiagonalTailChunk000Sub000Block165Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part008] using hcert

def TailChunk000Sub000Block165Part009SupportExplicit : Finset ℕ :=
  ([6847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part009 : ℚ :=
  (2486702419 : ℚ) / 194428160672563200

def SurrogateDiagonalTailChunk000Sub000Block165Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6847
    = surrogateDiagTailX0RatChunk000Sub000Block165Part009

theorem surrogateDiagonalTailChunk000Sub000Block165Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part009] using hcert

def TailChunk000Sub000Block165Part010SupportExplicit : Finset ℕ :=
  ([6851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part010 : ℚ :=
  (94678613341 : ℚ) / 110097329238835200

def SurrogateDiagonalTailChunk000Sub000Block165Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6851
    = surrogateDiagTailX0RatChunk000Sub000Block165Part010

theorem surrogateDiagonalTailChunk000Sub000Block165Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part010] using hcert

def TailChunk000Sub000Block165Part011SupportExplicit : Finset ℕ :=
  ([6853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part011 : ℚ :=
  (41972263499 : ℚ) / 38868031379865600

def SurrogateDiagonalTailChunk000Sub000Block165Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6853
    = surrogateDiagTailX0RatChunk000Sub000Block165Part011

theorem surrogateDiagonalTailChunk000Sub000Block165Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part011] using hcert

def TailChunk000Sub000Block165Part012SupportExplicit : Finset ℕ :=
  ([6854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part012 : ℚ :=
  (344008875025 : ℚ) / 70259402545254912

def SurrogateDiagonalTailChunk000Sub000Block165Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6854
    = surrogateDiagTailX0RatChunk000Sub000Block165Part012

theorem surrogateDiagonalTailChunk000Sub000Block165Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part012] using hcert

def TailChunk000Sub000Block165Part013SupportExplicit : Finset ℕ :=
  ([6855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part013 : ℚ :=
  (122611064425 : ℚ) / 36903276861456384

def SurrogateDiagonalTailChunk000Sub000Block165Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6855
    = surrogateDiagTailX0RatChunk000Sub000Block165Part013

theorem surrogateDiagonalTailChunk000Sub000Block165Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part013] using hcert

def TailChunk000Sub000Block165Part014SupportExplicit : Finset ℕ :=
  ([6857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part014 : ℚ :=
  (734663265625 : ℚ) / 1381179434669363712

def SurrogateDiagonalTailChunk000Sub000Block165Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6857
    = surrogateDiagTailX0RatChunk000Sub000Block165Part014

theorem surrogateDiagonalTailChunk000Sub000Block165Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part014] using hcert

def TailChunk000Sub000Block165Part015SupportExplicit : Finset ℕ :=
  ([6861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part015 : ℚ :=
  (408486855025 : ℚ) / 273144056223827232

def SurrogateDiagonalTailChunk000Sub000Block165Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6861
    = surrogateDiagTailX0RatChunk000Sub000Block165Part015

theorem surrogateDiagonalTailChunk000Sub000Block165Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part015] using hcert

def TailChunk000Sub000Block165Part016SupportExplicit : Finset ℕ :=
  ([6862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part016 : ℚ :=
  (234473866325 : ℚ) / 50146072121622528

def SurrogateDiagonalTailChunk000Sub000Block165Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6862
    = surrogateDiagTailX0RatChunk000Sub000Block165Part016

theorem surrogateDiagonalTailChunk000Sub000Block165Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part016] using hcert

def TailChunk000Sub000Block165Part017SupportExplicit : Finset ℕ :=
  ([6863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part017 : ℚ :=
  (735949515625 : ℚ) / 1386020719125292242

def SurrogateDiagonalTailChunk000Sub000Block165Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6863
    = surrogateDiagTailX0RatChunk000Sub000Block165Part017

theorem surrogateDiagonalTailChunk000Sub000Block165Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part017] using hcert

def TailChunk000Sub000Block165Part018SupportExplicit : Finset ℕ :=
  ([6865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part018 : ℚ :=
  (100917222825 : ℚ) / 108010002205278208

def SurrogateDiagonalTailChunk000Sub000Block165Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6865
    = surrogateDiagTailX0RatChunk000Sub000Block165Part018

theorem surrogateDiagonalTailChunk000Sub000Block165Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part018] using hcert

def TailChunk000Sub000Block165Part019SupportExplicit : Finset ℕ :=
  ([6866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part019 : ℚ :=
  (1472891487775 : ℚ) / 346909326325106688

def SurrogateDiagonalTailChunk000Sub000Block165Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6866
    = surrogateDiagTailX0RatChunk000Sub000Block165Part019

theorem surrogateDiagonalTailChunk000Sub000Block165Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part019] using hcert

def TailChunk000Sub000Block165Part020SupportExplicit : Finset ℕ :=
  ([6869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part020 : ℚ :=
  (737236890625 : ℚ) / 1390874719627421472

def SurrogateDiagonalTailChunk000Sub000Block165Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6869
    = surrogateDiagTailX0RatChunk000Sub000Block165Part020

theorem surrogateDiagonalTailChunk000Sub000Block165Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part020] using hcert

def TailChunk000Sub000Block165Part021SupportExplicit : Finset ℕ :=
  ([6870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part021 : ℚ :=
  (688157470075 : ℚ) / 27677457646092288

def SurrogateDiagonalTailChunk000Sub000Block165Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6870
    = surrogateDiagTailX0RatChunk000Sub000Block165Part021

theorem surrogateDiagonalTailChunk000Sub000Block165Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part021] using hcert

def TailChunk000Sub000Block165Part022SupportExplicit : Finset ℕ :=
  ([6871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part022 : ℚ :=
  (1180266025 : ℚ) / 2227992879083922

def SurrogateDiagonalTailChunk000Sub000Block165Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6871
    = surrogateDiagTailX0RatChunk000Sub000Block165Part022

theorem surrogateDiagonalTailChunk000Sub000Block165Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part022] using hcert

def TailChunk000Sub000Block165Part023SupportExplicit : Finset ℕ :=
  ([6873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part023 : ℚ :=
  (1553991844675 : ℚ) / 910243062639525888

def SurrogateDiagonalTailChunk000Sub000Block165Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6873
    = surrogateDiagTailX0RatChunk000Sub000Block165Part023

theorem surrogateDiagonalTailChunk000Sub000Block165Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part023] using hcert

def TailChunk000Sub000Block165Part024SupportExplicit : Finset ℕ :=
  ([6874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block165Part024 : ℚ :=
  (430007171 : ℚ) / 118613910038400

def SurrogateDiagonalTailChunk000Sub000Block165Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6874
    = surrogateDiagTailX0RatChunk000Sub000Block165Part024

theorem surrogateDiagonalTailChunk000Sub000Block165Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block165Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block165Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block165Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block165Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block165Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block165Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block165HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block165Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block165Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block165Part000
    + surrogateDiagTailX0RatChunk000Sub000Block165Part001
    + surrogateDiagTailX0RatChunk000Sub000Block165Part002
    + surrogateDiagTailX0RatChunk000Sub000Block165Part003
    + surrogateDiagTailX0RatChunk000Sub000Block165Part004
    + surrogateDiagTailX0RatChunk000Sub000Block165Part005
    + surrogateDiagTailX0RatChunk000Sub000Block165Part006
    + surrogateDiagTailX0RatChunk000Sub000Block165Part007
    + surrogateDiagTailX0RatChunk000Sub000Block165Part008
    + surrogateDiagTailX0RatChunk000Sub000Block165Part009

def surrogateDiagonalTailChunk000Sub000Block165MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block165Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block165Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block165Part010
    + surrogateDiagTailX0RatChunk000Sub000Block165Part011
    + surrogateDiagTailX0RatChunk000Sub000Block165Part012
    + surrogateDiagTailX0RatChunk000Sub000Block165Part013
    + surrogateDiagTailX0RatChunk000Sub000Block165Part014
    + surrogateDiagTailX0RatChunk000Sub000Block165Part015
    + surrogateDiagTailX0RatChunk000Sub000Block165Part016
    + surrogateDiagTailX0RatChunk000Sub000Block165Part017
    + surrogateDiagTailX0RatChunk000Sub000Block165Part018
    + surrogateDiagTailX0RatChunk000Sub000Block165Part019

def surrogateDiagonalTailChunk000Sub000Block165TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block165Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block165Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block165Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block165Part020
    + surrogateDiagTailX0RatChunk000Sub000Block165Part021
    + surrogateDiagTailX0RatChunk000Sub000Block165Part022
    + surrogateDiagTailX0RatChunk000Sub000Block165Part023
    + surrogateDiagTailX0RatChunk000Sub000Block165Part024

def surrogateDiagonalTailChunk000Sub000Block165Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block165HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block165MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block165TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block165 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block165Part000
    + surrogateDiagTailX0RatChunk000Sub000Block165Part001
    + surrogateDiagTailX0RatChunk000Sub000Block165Part002
    + surrogateDiagTailX0RatChunk000Sub000Block165Part003
    + surrogateDiagTailX0RatChunk000Sub000Block165Part004
    + surrogateDiagTailX0RatChunk000Sub000Block165Part005
    + surrogateDiagTailX0RatChunk000Sub000Block165Part006
    + surrogateDiagTailX0RatChunk000Sub000Block165Part007
    + surrogateDiagTailX0RatChunk000Sub000Block165Part008
    + surrogateDiagTailX0RatChunk000Sub000Block165Part009
    + surrogateDiagTailX0RatChunk000Sub000Block165Part010
    + surrogateDiagTailX0RatChunk000Sub000Block165Part011
    + surrogateDiagTailX0RatChunk000Sub000Block165Part012
    + surrogateDiagTailX0RatChunk000Sub000Block165Part013
    + surrogateDiagTailX0RatChunk000Sub000Block165Part014
    + surrogateDiagTailX0RatChunk000Sub000Block165Part015
    + surrogateDiagTailX0RatChunk000Sub000Block165Part016
    + surrogateDiagTailX0RatChunk000Sub000Block165Part017
    + surrogateDiagTailX0RatChunk000Sub000Block165Part018
    + surrogateDiagTailX0RatChunk000Sub000Block165Part019
    + surrogateDiagTailX0RatChunk000Sub000Block165Part020
    + surrogateDiagTailX0RatChunk000Sub000Block165Part021
    + surrogateDiagTailX0RatChunk000Sub000Block165Part022
    + surrogateDiagTailX0RatChunk000Sub000Block165Part023
    + surrogateDiagTailX0RatChunk000Sub000Block165Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block165_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block165Head + surrogateDiagTailX0RatChunk000Sub000Block165Mid + surrogateDiagTailX0RatChunk000Sub000Block165Tail =
      surrogateDiagTailX0RatChunk000Sub000Block165 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block165Head surrogateDiagTailX0RatChunk000Sub000Block165Mid surrogateDiagTailX0RatChunk000Sub000Block165Tail surrogateDiagTailX0RatChunk000Sub000Block165
  ring

def SurrogateDiagonalTailChunk000Sub000Block165HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block165HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block165Head

def SurrogateDiagonalTailChunk000Sub000Block165MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block165MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block165Mid

def SurrogateDiagonalTailChunk000Sub000Block165TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block165TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block165Tail

theorem surrogateDiagonalTailChunk000Sub000Block165_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block165HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block165MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block165TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block165Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block165 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block165HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block165MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block165TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block165Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block165_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
