import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [8,9). -/

/-- Block 008 covers tail-support indices [5200,5225) and q from 8601 to 8639. -/

def TailChunk000Sub001Block008Part000SupportExplicit : Finset ℕ :=
  ([8601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part000 : ℚ :=
  (40658992399 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk000Sub001Block008Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8601
    = surrogateDiagTailX0RatChunk000Sub001Block008Part000

theorem surrogateDiagonalTailChunk000Sub001Block008Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part000] using hcert

def TailChunk000Sub001Block008Part001SupportExplicit : Finset ℕ :=
  ([8602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part001 : ℚ :=
  (39163082929 : ℚ) / 15355271656243200

def SurrogateDiagonalTailChunk000Sub001Block008Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8602
    = surrogateDiagTailX0RatChunk000Sub001Block008Part001

theorem surrogateDiagonalTailChunk000Sub001Block008Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part001] using hcert

def TailChunk000Sub001Block008Part002SupportExplicit : Finset ℕ :=
  ([8603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part002 : ℚ :=
  (378644241925 : ℚ) / 7369284573591717888

def SurrogateDiagonalTailChunk000Sub001Block008Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8603
    = surrogateDiagTailX0RatChunk000Sub001Block008Part002

theorem surrogateDiagonalTailChunk000Sub001Block008Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part002] using hcert

def TailChunk000Sub001Block008Part003SupportExplicit : Finset ℕ :=
  ([8605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part003 : ℚ :=
  (11114565581 : ℚ) / 112049676622233600

def SurrogateDiagonalTailChunk000Sub001Block008Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8605
    = surrogateDiagTailX0RatChunk000Sub001Block008Part003

theorem surrogateDiagonalTailChunk000Sub001Block008Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part003] using hcert

def TailChunk000Sub001Block008Part004SupportExplicit : Finset ℕ :=
  ([8606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part004 : ℚ :=
  (4797072919 : ℚ) / 2732908456396800

def SurrogateDiagonalTailChunk000Sub001Block008Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8606
    = surrogateDiagTailX0RatChunk000Sub001Block008Part004

theorem surrogateDiagonalTailChunk000Sub001Block008Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part004] using hcert

def TailChunk000Sub001Block008Part005SupportExplicit : Finset ℕ :=
  ([8607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part005 : ℚ :=
  (1499640953 : ℚ) / 3149909856000000

def SurrogateDiagonalTailChunk000Sub001Block008Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8607
    = surrogateDiagTailX0RatChunk000Sub001Block008Part005

theorem surrogateDiagonalTailChunk000Sub001Block008Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part005] using hcert

def TailChunk000Sub001Block008Part006SupportExplicit : Finset ℕ :=
  ([8609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block008Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8609
    = surrogateDiagTailX0RatChunk000Sub001Block008Part006

theorem surrogateDiagonalTailChunk000Sub001Block008Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part006] using hcert

def TailChunk000Sub001Block008Part007SupportExplicit : Finset ℕ :=
  ([8610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part007 : ℚ :=
  (1218922309 : ℚ) / 75512571494400

def SurrogateDiagonalTailChunk000Sub001Block008Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8610
    = surrogateDiagTailX0RatChunk000Sub001Block008Part007

theorem surrogateDiagonalTailChunk000Sub001Block008Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part007] using hcert

def TailChunk000Sub001Block008Part008SupportExplicit : Finset ℕ :=
  ([8611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part008 : ℚ :=
  (2211377225 : ℚ) / 484313911122981888

def SurrogateDiagonalTailChunk000Sub001Block008Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8611
    = surrogateDiagTailX0RatChunk000Sub001Block008Part008

theorem surrogateDiagonalTailChunk000Sub001Block008Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part008] using hcert

def TailChunk000Sub001Block008Part009SupportExplicit : Finset ℕ :=
  ([8614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part009 : ℚ :=
  (282457089025 : ℚ) / 190111692190851072

def SurrogateDiagonalTailChunk000Sub001Block008Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8614
    = surrogateDiagTailX0RatChunk000Sub001Block008Part009

theorem surrogateDiagonalTailChunk000Sub001Block008Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part009] using hcert

def TailChunk000Sub001Block008Part010SupportExplicit : Finset ℕ :=
  ([8615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part010 : ℚ :=
  (19893518275 : ℚ) / 201020977885625856

def SurrogateDiagonalTailChunk000Sub001Block008Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8615
    = surrogateDiagTailX0RatChunk000Sub001Block008Part010

theorem surrogateDiagonalTailChunk000Sub001Block008Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part010] using hcert

def TailChunk000Sub001Block008Part011SupportExplicit : Finset ℕ :=
  ([8617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part011 : ℚ :=
  (15194900173 : ℚ) / 296696414153347200

def SurrogateDiagonalTailChunk000Sub001Block008Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8617
    = surrogateDiagTailX0RatChunk000Sub001Block008Part011

theorem surrogateDiagonalTailChunk000Sub001Block008Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part011] using hcert

def TailChunk000Sub001Block008Part012SupportExplicit : Finset ℕ :=
  ([8618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part012 : ℚ :=
  (561201317 : ℚ) / 367280801672040

def SurrogateDiagonalTailChunk000Sub001Block008Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8618
    = surrogateDiagTailX0RatChunk000Sub001Block008Part012

theorem surrogateDiagonalTailChunk000Sub001Block008Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part012] using hcert

def TailChunk000Sub001Block008Part013SupportExplicit : Finset ℕ :=
  ([8621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part013 : ℚ :=
  (246793328275 : ℚ) / 675952683345248256

def SurrogateDiagonalTailChunk000Sub001Block008Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8621
    = surrogateDiagTailX0RatChunk000Sub001Block008Part013

theorem surrogateDiagonalTailChunk000Sub001Block008Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part013] using hcert

def TailChunk000Sub001Block008Part014SupportExplicit : Finset ℕ :=
  ([8623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part014 : ℚ :=
  (1161814515625 : ℚ) / 3454609330187705682

def SurrogateDiagonalTailChunk000Sub001Block008Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8623
    = surrogateDiagTailX0RatChunk000Sub001Block008Part014

theorem surrogateDiagonalTailChunk000Sub001Block008Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part014] using hcert

def TailChunk000Sub001Block008Part015SupportExplicit : Finset ℕ :=
  ([8626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part015 : ℚ :=
  (712755156475 : ℚ) / 228259773070528896

def SurrogateDiagonalTailChunk000Sub001Block008Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8626
    = surrogateDiagTailX0RatChunk000Sub001Block008Part015

theorem surrogateDiagonalTailChunk000Sub001Block008Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part015] using hcert

def TailChunk000Sub001Block008Part016SupportExplicit : Finset ℕ :=
  ([8627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part016 : ℚ :=
  (1162892640625 : ℚ) / 3461024573270963922

def SurrogateDiagonalTailChunk000Sub001Block008Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8627
    = surrogateDiagTailX0RatChunk000Sub001Block008Part016

theorem surrogateDiagonalTailChunk000Sub001Block008Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part016] using hcert

def TailChunk000Sub001Block008Part017SupportExplicit : Finset ℕ :=
  ([8629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part017 : ℚ :=
  (1163431890625 : ℚ) / 3464235543319110432

def SurrogateDiagonalTailChunk000Sub001Block008Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8629
    = surrogateDiagTailX0RatChunk000Sub001Block008Part017

theorem surrogateDiagonalTailChunk000Sub001Block008Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part017] using hcert

def TailChunk000Sub001Block008Part018SupportExplicit : Finset ℕ :=
  ([8630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part018 : ℚ :=
  (836641880375 : ℚ) / 176711938820219904

def SurrogateDiagonalTailChunk000Sub001Block008Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8630
    = surrogateDiagTailX0RatChunk000Sub001Block008Part018

theorem surrogateDiagonalTailChunk000Sub001Block008Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part018] using hcert

def TailChunk000Sub001Block008Part019SupportExplicit : Finset ℕ :=
  ([8633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part019 : ℚ :=
  (205367211925 : ℚ) / 578921660116107264

def SurrogateDiagonalTailChunk000Sub001Block008Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8633
    = surrogateDiagTailX0RatChunk000Sub001Block008Part019

theorem surrogateDiagonalTailChunk000Sub001Block008Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part019] using hcert

def TailChunk000Sub001Block008Part020SupportExplicit : Finset ℕ :=
  ([8634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part020 : ℚ :=
  (77606625 : ℚ) / 17103915233344

def SurrogateDiagonalTailChunk000Sub001Block008Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8634
    = surrogateDiagTailX0RatChunk000Sub001Block008Part020

theorem surrogateDiagonalTailChunk000Sub001Block008Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part020] using hcert

def TailChunk000Sub001Block008Part021SupportExplicit : Finset ℕ :=
  ([8635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part021 : ℚ :=
  (4510255421 : ℚ) / 5832461234995200

def SurrogateDiagonalTailChunk000Sub001Block008Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8635
    = surrogateDiagTailX0RatChunk000Sub001Block008Part021

theorem surrogateDiagonalTailChunk000Sub001Block008Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part021] using hcert

def TailChunk000Sub001Block008Part022SupportExplicit : Finset ℕ :=
  ([8637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part022 : ℚ :=
  (647360064925 : ℚ) / 686198885909274912

def SurrogateDiagonalTailChunk000Sub001Block008Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8637
    = surrogateDiagTailX0RatChunk000Sub001Block008Part022

theorem surrogateDiagonalTailChunk000Sub001Block008Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part022] using hcert

def TailChunk000Sub001Block008Part023SupportExplicit : Finset ℕ :=
  ([8638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part023 : ℚ :=
  (255464842375 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub001Block008Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8638
    = surrogateDiagTailX0RatChunk000Sub001Block008Part023

theorem surrogateDiagonalTailChunk000Sub001Block008Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part023] using hcert

def TailChunk000Sub001Block008Part024SupportExplicit : Finset ℕ :=
  ([8639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block008Part024 : ℚ :=
  (750229444675 : ℚ) / 2098693614866254848

def SurrogateDiagonalTailChunk000Sub001Block008Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8639
    = surrogateDiagTailX0RatChunk000Sub001Block008Part024

theorem surrogateDiagonalTailChunk000Sub001Block008Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block008Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block008Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block008Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block008Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block008Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block008HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block008Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block008Part000
    + surrogateDiagTailX0RatChunk000Sub001Block008Part001
    + surrogateDiagTailX0RatChunk000Sub001Block008Part002
    + surrogateDiagTailX0RatChunk000Sub001Block008Part003
    + surrogateDiagTailX0RatChunk000Sub001Block008Part004
    + surrogateDiagTailX0RatChunk000Sub001Block008Part005
    + surrogateDiagTailX0RatChunk000Sub001Block008Part006
    + surrogateDiagTailX0RatChunk000Sub001Block008Part007
    + surrogateDiagTailX0RatChunk000Sub001Block008Part008
    + surrogateDiagTailX0RatChunk000Sub001Block008Part009

def surrogateDiagonalTailChunk000Sub001Block008MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block008Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block008Part010
    + surrogateDiagTailX0RatChunk000Sub001Block008Part011
    + surrogateDiagTailX0RatChunk000Sub001Block008Part012
    + surrogateDiagTailX0RatChunk000Sub001Block008Part013
    + surrogateDiagTailX0RatChunk000Sub001Block008Part014
    + surrogateDiagTailX0RatChunk000Sub001Block008Part015
    + surrogateDiagTailX0RatChunk000Sub001Block008Part016
    + surrogateDiagTailX0RatChunk000Sub001Block008Part017
    + surrogateDiagTailX0RatChunk000Sub001Block008Part018
    + surrogateDiagTailX0RatChunk000Sub001Block008Part019

def surrogateDiagonalTailChunk000Sub001Block008TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block008Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block008Part020
    + surrogateDiagTailX0RatChunk000Sub001Block008Part021
    + surrogateDiagTailX0RatChunk000Sub001Block008Part022
    + surrogateDiagTailX0RatChunk000Sub001Block008Part023
    + surrogateDiagTailX0RatChunk000Sub001Block008Part024

def surrogateDiagonalTailChunk000Sub001Block008Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block008HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block008MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block008TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block008 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block008Part000
    + surrogateDiagTailX0RatChunk000Sub001Block008Part001
    + surrogateDiagTailX0RatChunk000Sub001Block008Part002
    + surrogateDiagTailX0RatChunk000Sub001Block008Part003
    + surrogateDiagTailX0RatChunk000Sub001Block008Part004
    + surrogateDiagTailX0RatChunk000Sub001Block008Part005
    + surrogateDiagTailX0RatChunk000Sub001Block008Part006
    + surrogateDiagTailX0RatChunk000Sub001Block008Part007
    + surrogateDiagTailX0RatChunk000Sub001Block008Part008
    + surrogateDiagTailX0RatChunk000Sub001Block008Part009
    + surrogateDiagTailX0RatChunk000Sub001Block008Part010
    + surrogateDiagTailX0RatChunk000Sub001Block008Part011
    + surrogateDiagTailX0RatChunk000Sub001Block008Part012
    + surrogateDiagTailX0RatChunk000Sub001Block008Part013
    + surrogateDiagTailX0RatChunk000Sub001Block008Part014
    + surrogateDiagTailX0RatChunk000Sub001Block008Part015
    + surrogateDiagTailX0RatChunk000Sub001Block008Part016
    + surrogateDiagTailX0RatChunk000Sub001Block008Part017
    + surrogateDiagTailX0RatChunk000Sub001Block008Part018
    + surrogateDiagTailX0RatChunk000Sub001Block008Part019
    + surrogateDiagTailX0RatChunk000Sub001Block008Part020
    + surrogateDiagTailX0RatChunk000Sub001Block008Part021
    + surrogateDiagTailX0RatChunk000Sub001Block008Part022
    + surrogateDiagTailX0RatChunk000Sub001Block008Part023
    + surrogateDiagTailX0RatChunk000Sub001Block008Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block008_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block008Head + surrogateDiagTailX0RatChunk000Sub001Block008Mid + surrogateDiagTailX0RatChunk000Sub001Block008Tail =
      surrogateDiagTailX0RatChunk000Sub001Block008 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block008Head surrogateDiagTailX0RatChunk000Sub001Block008Mid surrogateDiagTailX0RatChunk000Sub001Block008Tail surrogateDiagTailX0RatChunk000Sub001Block008
  ring

def SurrogateDiagonalTailChunk000Sub001Block008HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block008HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block008Head

def SurrogateDiagonalTailChunk000Sub001Block008MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block008MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block008Mid

def SurrogateDiagonalTailChunk000Sub001Block008TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block008TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block008Tail

theorem surrogateDiagonalTailChunk000Sub001Block008_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block008HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block008MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block008TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block008Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block008 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block008HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block008MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block008TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block008Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block008_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
