import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [125,126). -/

/- Block 125 covers tail-support indices [3125,3150) and q from 5190 to 5231. -/

def TailChunk000Sub000Block125Part000SupportExplicit : Finset ℕ :=
  ([5190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part000 : ℚ :=
  (138913099125 : ℚ) / 2987991376592896

def SurrogateDiagonalTailChunk000Sub000Block125Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5190
    = surrogateDiagTailX0RatChunk000Sub000Block125Part000

theorem surrogateDiagonalTailChunk000Sub000Block125Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part000] using hcert

def TailChunk000Sub000Block125Part001SupportExplicit : Finset ℕ :=
  ([5191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part001 : ℚ :=
  (538328115525 : ℚ) / 514301438174304256

def SurrogateDiagonalTailChunk000Sub000Block125Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5191
    = surrogateDiagTailX0RatChunk000Sub000Block125Part001

theorem surrogateDiagonalTailChunk000Sub000Block125Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part001] using hcert

def TailChunk000Sub000Block125Part002SupportExplicit : Finset ℕ :=
  ([5195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part002 : ℚ :=
  (674162180375 : ℚ) / 371557680080200704

def SurrogateDiagonalTailChunk000Sub000Block125Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5195
    = surrogateDiagTailX0RatChunk000Sub000Block125Part002

theorem surrogateDiagonalTailChunk000Sub000Block125Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part002] using hcert

def TailChunk000Sub000Block125Part003SupportExplicit : Finset ℕ :=
  ([5197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part003 : ℚ :=
  (422012640625 : ℚ) / 455662655876473632

def SurrogateDiagonalTailChunk000Sub000Block125Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5197
    = surrogateDiagTailX0RatChunk000Sub000Block125Part003

theorem surrogateDiagonalTailChunk000Sub000Block125Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part003] using hcert

def TailChunk000Sub000Block125Part004SupportExplicit : Finset ℕ :=
  ([5198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part004 : ℚ :=
  (33315989925 : ℚ) / 3840417421524992

def SurrogateDiagonalTailChunk000Sub000Block125Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5198
    = surrogateDiagTailX0RatChunk000Sub000Block125Part004

theorem surrogateDiagonalTailChunk000Sub000Block125Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part004] using hcert

def TailChunk000Sub000Block125Part005SupportExplicit : Finset ℕ :=
  ([5199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part005 : ℚ :=
  (112555875 : ℚ) / 35995776123904

def SurrogateDiagonalTailChunk000Sub000Block125Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5199
    = surrogateDiagTailX0RatChunk000Sub000Block125Part005

theorem surrogateDiagonalTailChunk000Sub000Block125Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part005] using hcert

def TailChunk000Sub000Block125Part006SupportExplicit : Finset ℕ :=
  ([5201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part006 : ℚ :=
  (11487235975 : ℚ) / 7796091657590208

def SurrogateDiagonalTailChunk000Sub000Block125Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5201
    = surrogateDiagTailX0RatChunk000Sub000Block125Part006

theorem surrogateDiagonalTailChunk000Sub000Block125Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part006] using hcert

def TailChunk000Sub000Block125Part007SupportExplicit : Finset ℕ :=
  ([5205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part007 : ℚ :=
  (900542696275 : ℚ) / 146788219290943488

def SurrogateDiagonalTailChunk000Sub000Block125Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5205
    = surrogateDiagTailX0RatChunk000Sub000Block125Part007

theorem surrogateDiagonalTailChunk000Sub000Block125Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part007] using hcert

def TailChunk000Sub000Block125Part008SupportExplicit : Finset ℕ :=
  ([5206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part008 : ℚ :=
  (265095321475 : ℚ) / 29933069776551936

def SurrogateDiagonalTailChunk000Sub000Block125Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5206
    = surrogateDiagTailX0RatChunk000Sub000Block125Part008

theorem surrogateDiagonalTailChunk000Sub000Block125Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part008] using hcert

def TailChunk000Sub000Block125Part009SupportExplicit : Finset ℕ :=
  ([5207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part009 : ℚ :=
  (31814821 : ℚ) / 1008391141900800

def SurrogateDiagonalTailChunk000Sub000Block125Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5207
    = surrogateDiagTailX0RatChunk000Sub000Block125Part009

theorem surrogateDiagonalTailChunk000Sub000Block125Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part009] using hcert

def TailChunk000Sub000Block125Part010SupportExplicit : Finset ℕ :=
  ([5209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part010 : ℚ :=
  (423963765625 : ℚ) / 459886615189811712

def SurrogateDiagonalTailChunk000Sub000Block125Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5209
    = surrogateDiagTailX0RatChunk000Sub000Block125Part010

theorem surrogateDiagonalTailChunk000Sub000Block125Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part010] using hcert

def TailChunk000Sub000Block125Part011SupportExplicit : Finset ℕ :=
  ([5210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part011 : ℚ :=
  (1354767899 : ℚ) / 93607402536960

def SurrogateDiagonalTailChunk000Sub000Block125Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5210
    = surrogateDiagTailX0RatChunk000Sub000Block125Part011

theorem surrogateDiagonalTailChunk000Sub000Block125Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part011] using hcert

def TailChunk000Sub000Block125Part012SupportExplicit : Finset ℕ :=
  ([5213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part012 : ℚ :=
  (31281129971 : ℚ) / 26547388416000000

def SurrogateDiagonalTailChunk000Sub000Block125Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5213
    = surrogateDiagTailX0RatChunk000Sub000Block125Part012

theorem surrogateDiagonalTailChunk000Sub000Block125Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part012] using hcert

def TailChunk000Sub000Block125Part013SupportExplicit : Finset ℕ :=
  ([5214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part013 : ℚ :=
  (778353041 : ℚ) / 22783051699200

def SurrogateDiagonalTailChunk000Sub000Block125Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5214
    = surrogateDiagTailX0RatChunk000Sub000Block125Part013

theorem surrogateDiagonalTailChunk000Sub000Block125Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part013] using hcert

def TailChunk000Sub000Block125Part014SupportExplicit : Finset ℕ :=
  ([5215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part014 : ℚ :=
  (4436454175 : ℚ) / 1554815000659968

def SurrogateDiagonalTailChunk000Sub000Block125Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5215
    = surrogateDiagTailX0RatChunk000Sub000Block125Part014

theorem surrogateDiagonalTailChunk000Sub000Block125Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part014] using hcert

def TailChunk000Sub000Block125Part015SupportExplicit : Finset ℕ :=
  ([5217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part015 : ℚ :=
  (1077682153225 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub000Block125Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5217
    = surrogateDiagTailX0RatChunk000Sub000Block125Part015

theorem surrogateDiagonalTailChunk000Sub000Block125Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part015] using hcert

def TailChunk000Sub000Block125Part016SupportExplicit : Finset ℕ :=
  ([5218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part016 : ℚ :=
  (850689952975 : ℚ) / 115679714238824448

def SurrogateDiagonalTailChunk000Sub000Block125Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5218
    = surrogateDiagTailX0RatChunk000Sub000Block125Part016

theorem surrogateDiagonalTailChunk000Sub000Block125Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part016] using hcert

def TailChunk000Sub000Block125Part017SupportExplicit : Finset ℕ :=
  ([5219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part017 : ℚ :=
  (795628993475 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk000Sub000Block125Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5219
    = surrogateDiagTailX0RatChunk000Sub000Block125Part017

theorem surrogateDiagonalTailChunk000Sub000Block125Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part017] using hcert

def TailChunk000Sub000Block125Part018SupportExplicit : Finset ℕ :=
  ([5221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part018 : ℚ :=
  (539747006325 : ℚ) / 509366154172475776

def SurrogateDiagonalTailChunk000Sub000Block125Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5221
    = surrogateDiagTailX0RatChunk000Sub000Block125Part018

theorem surrogateDiagonalTailChunk000Sub000Block125Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part018] using hcert

def TailChunk000Sub000Block125Part019SupportExplicit : Finset ℕ :=
  ([5222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part019 : ℚ :=
  (359939215025 : ℚ) / 31029417601311744

def SurrogateDiagonalTailChunk000Sub000Block125Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5222
    = surrogateDiagTailX0RatChunk000Sub000Block125Part019

theorem surrogateDiagonalTailChunk000Sub000Block125Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part019] using hcert

def TailChunk000Sub000Block125Part020SupportExplicit : Finset ℕ :=
  ([5223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part020 : ℚ :=
  (1514633 : ℚ) / 488872627200

def SurrogateDiagonalTailChunk000Sub000Block125Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5223
    = surrogateDiagTailX0RatChunk000Sub000Block125Part020

theorem surrogateDiagonalTailChunk000Sub000Block125Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part020] using hcert

def TailChunk000Sub000Block125Part021SupportExplicit : Finset ℕ :=
  ([5226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part021 : ℚ :=
  (43323877475 : ℚ) / 1431050246258688

def SurrogateDiagonalTailChunk000Sub000Block125Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5226
    = surrogateDiagTailX0RatChunk000Sub000Block125Part021

theorem surrogateDiagonalTailChunk000Sub000Block125Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part021] using hcert

def TailChunk000Sub000Block125Part022SupportExplicit : Finset ℕ :=
  ([5227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part022 : ℚ :=
  (426898890625 : ℚ) / 466277532032644722

def SurrogateDiagonalTailChunk000Sub000Block125Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5227
    = surrogateDiagTailX0RatChunk000Sub000Block125Part022

theorem surrogateDiagonalTailChunk000Sub000Block125Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part022] using hcert

def TailChunk000Sub000Block125Part023SupportExplicit : Finset ℕ :=
  ([5230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part023 : ℚ :=
  (12325148725 : ℚ) / 880146723105792

def SurrogateDiagonalTailChunk000Sub000Block125Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5230
    = surrogateDiagTailX0RatChunk000Sub000Block125Part023

theorem surrogateDiagonalTailChunk000Sub000Block125Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part023] using hcert

def TailChunk000Sub000Block125Part024SupportExplicit : Finset ℕ :=
  ([5231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block125Part024 : ℚ :=
  (684084025 : ℚ) / 748330774637682

def SurrogateDiagonalTailChunk000Sub000Block125Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5231
    = surrogateDiagTailX0RatChunk000Sub000Block125Part024

theorem surrogateDiagonalTailChunk000Sub000Block125Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block125Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block125Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block125Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block125Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block125Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block125Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block125HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block125Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block125Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block125Part000
    + surrogateDiagTailX0RatChunk000Sub000Block125Part001
    + surrogateDiagTailX0RatChunk000Sub000Block125Part002
    + surrogateDiagTailX0RatChunk000Sub000Block125Part003
    + surrogateDiagTailX0RatChunk000Sub000Block125Part004
    + surrogateDiagTailX0RatChunk000Sub000Block125Part005
    + surrogateDiagTailX0RatChunk000Sub000Block125Part006
    + surrogateDiagTailX0RatChunk000Sub000Block125Part007
    + surrogateDiagTailX0RatChunk000Sub000Block125Part008
    + surrogateDiagTailX0RatChunk000Sub000Block125Part009

def surrogateDiagonalTailChunk000Sub000Block125MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block125Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block125Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block125Part010
    + surrogateDiagTailX0RatChunk000Sub000Block125Part011
    + surrogateDiagTailX0RatChunk000Sub000Block125Part012
    + surrogateDiagTailX0RatChunk000Sub000Block125Part013
    + surrogateDiagTailX0RatChunk000Sub000Block125Part014
    + surrogateDiagTailX0RatChunk000Sub000Block125Part015
    + surrogateDiagTailX0RatChunk000Sub000Block125Part016
    + surrogateDiagTailX0RatChunk000Sub000Block125Part017
    + surrogateDiagTailX0RatChunk000Sub000Block125Part018
    + surrogateDiagTailX0RatChunk000Sub000Block125Part019

def surrogateDiagonalTailChunk000Sub000Block125TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block125Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block125Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block125Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block125Part020
    + surrogateDiagTailX0RatChunk000Sub000Block125Part021
    + surrogateDiagTailX0RatChunk000Sub000Block125Part022
    + surrogateDiagTailX0RatChunk000Sub000Block125Part023
    + surrogateDiagTailX0RatChunk000Sub000Block125Part024

def surrogateDiagonalTailChunk000Sub000Block125Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block125HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block125MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block125TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block125 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block125Part000
    + surrogateDiagTailX0RatChunk000Sub000Block125Part001
    + surrogateDiagTailX0RatChunk000Sub000Block125Part002
    + surrogateDiagTailX0RatChunk000Sub000Block125Part003
    + surrogateDiagTailX0RatChunk000Sub000Block125Part004
    + surrogateDiagTailX0RatChunk000Sub000Block125Part005
    + surrogateDiagTailX0RatChunk000Sub000Block125Part006
    + surrogateDiagTailX0RatChunk000Sub000Block125Part007
    + surrogateDiagTailX0RatChunk000Sub000Block125Part008
    + surrogateDiagTailX0RatChunk000Sub000Block125Part009
    + surrogateDiagTailX0RatChunk000Sub000Block125Part010
    + surrogateDiagTailX0RatChunk000Sub000Block125Part011
    + surrogateDiagTailX0RatChunk000Sub000Block125Part012
    + surrogateDiagTailX0RatChunk000Sub000Block125Part013
    + surrogateDiagTailX0RatChunk000Sub000Block125Part014
    + surrogateDiagTailX0RatChunk000Sub000Block125Part015
    + surrogateDiagTailX0RatChunk000Sub000Block125Part016
    + surrogateDiagTailX0RatChunk000Sub000Block125Part017
    + surrogateDiagTailX0RatChunk000Sub000Block125Part018
    + surrogateDiagTailX0RatChunk000Sub000Block125Part019
    + surrogateDiagTailX0RatChunk000Sub000Block125Part020
    + surrogateDiagTailX0RatChunk000Sub000Block125Part021
    + surrogateDiagTailX0RatChunk000Sub000Block125Part022
    + surrogateDiagTailX0RatChunk000Sub000Block125Part023
    + surrogateDiagTailX0RatChunk000Sub000Block125Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block125_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block125Head + surrogateDiagTailX0RatChunk000Sub000Block125Mid + surrogateDiagTailX0RatChunk000Sub000Block125Tail =
      surrogateDiagTailX0RatChunk000Sub000Block125 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block125Head surrogateDiagTailX0RatChunk000Sub000Block125Mid surrogateDiagTailX0RatChunk000Sub000Block125Tail surrogateDiagTailX0RatChunk000Sub000Block125
  ring

def SurrogateDiagonalTailChunk000Sub000Block125HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block125HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block125Head

def SurrogateDiagonalTailChunk000Sub000Block125MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block125MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block125Mid

def SurrogateDiagonalTailChunk000Sub000Block125TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block125TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block125Tail

theorem surrogateDiagonalTailChunk000Sub000Block125_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block125HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block125MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block125TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block125Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block125 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block125HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block125MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block125TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block125Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block125_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
