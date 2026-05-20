import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [80,81). -/

/- Block 080 covers tail-support indices [2000,2025) and q from 3337 to 3377. -/

def TailChunk000Sub000Block080Part000SupportExplicit : Finset ℕ :=
  ([3337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part000 : ℚ :=
  (53246390581 : ℚ) / 10752521930371200

def SurrogateDiagonalTailChunk000Sub000Block080Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3337
    = surrogateDiagTailX0RatChunk000Sub000Block080Part000

theorem surrogateDiagonalTailChunk000Sub000Block080Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part000] using hcert

def TailChunk000Sub000Block080Part001SupportExplicit : Finset ℕ :=
  ([3338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part001 : ℚ :=
  (58009307825 : ℚ) / 2150644038959232

def SurrogateDiagonalTailChunk000Sub000Block080Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3338
    = surrogateDiagTailX0RatChunk000Sub000Block080Part001

theorem surrogateDiagonalTailChunk000Sub000Block080Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part001] using hcert

def TailChunk000Sub000Block080Part002SupportExplicit : Finset ℕ :=
  ([3341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part002 : ℚ :=
  (1253224765075 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub000Block080Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3341
    = surrogateDiagTailX0RatChunk000Sub000Block080Part002

theorem surrogateDiagonalTailChunk000Sub000Block080Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part002] using hcert

def TailChunk000Sub000Block080Part003SupportExplicit : Finset ℕ :=
  ([3342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part003 : ℚ :=
  (4355025 : ℚ) / 47782533248

def SurrogateDiagonalTailChunk000Sub000Block080Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3342
    = surrogateDiagTailX0RatChunk000Sub000Block080Part003

theorem surrogateDiagonalTailChunk000Sub000Block080Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part003] using hcert

def TailChunk000Sub000Block080Part004SupportExplicit : Finset ℕ :=
  ([3343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part004 : ℚ :=
  (1396676733775 : ℚ) / 311926764961656648

def SurrogateDiagonalTailChunk000Sub000Block080Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3343
    = surrogateDiagTailX0RatChunk000Sub000Block080Part004

theorem surrogateDiagonalTailChunk000Sub000Block080Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part004] using hcert

def TailChunk000Sub000Block080Part005SupportExplicit : Finset ℕ :=
  ([3345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part005 : ℚ :=
  (152816608175 : ℚ) / 8292346670186496

def SurrogateDiagonalTailChunk000Sub000Block080Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3345
    = surrogateDiagTailX0RatChunk000Sub000Block080Part005

theorem surrogateDiagonalTailChunk000Sub000Block080Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part005] using hcert

def TailChunk000Sub000Block080Part006SupportExplicit : Finset ℕ :=
  ([3346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part006 : ℚ :=
  (444486022525 : ℚ) / 10397757600332928

def SurrogateDiagonalTailChunk000Sub000Block080Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3346
    = surrogateDiagTailX0RatChunk000Sub000Block080Part006

theorem surrogateDiagonalTailChunk000Sub000Block080Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part006] using hcert

def TailChunk000Sub000Block080Part007SupportExplicit : Finset ℕ :=
  ([3347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part007 : ℚ :=
  (175037640625 : ℚ) / 78355703477504082

def SurrogateDiagonalTailChunk000Sub000Block080Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3347
    = surrogateDiagTailX0RatChunk000Sub000Block080Part007

theorem surrogateDiagonalTailChunk000Sub000Block080Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part007] using hcert

def TailChunk000Sub000Block080Part008SupportExplicit : Finset ℕ :=
  ([3349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part008 : ℚ :=
  (677365210525 : ℚ) / 241841637590827008

def SurrogateDiagonalTailChunk000Sub000Block080Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3349
    = surrogateDiagTailX0RatChunk000Sub000Block080Part008

theorem surrogateDiagonalTailChunk000Sub000Block080Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part008] using hcert

def TailChunk000Sub000Block080Part009SupportExplicit : Finset ℕ :=
  ([3351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part009 : ℚ :=
  (623414911075 : ℚ) / 62058835202623488

def SurrogateDiagonalTailChunk000Sub000Block080Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3351
    = surrogateDiagTailX0RatChunk000Sub000Block080Part009

theorem surrogateDiagonalTailChunk000Sub000Block080Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part009] using hcert

def TailChunk000Sub000Block080Part010SupportExplicit : Finset ℕ :=
  ([3353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part010 : ℚ :=
  (164712267625 : ℚ) / 42294457187357472

def SurrogateDiagonalTailChunk000Sub000Block080Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3353
    = surrogateDiagTailX0RatChunk000Sub000Block080Part010

theorem surrogateDiagonalTailChunk000Sub000Block080Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part010] using hcert

def TailChunk000Sub000Block080Part011SupportExplicit : Finset ℕ :=
  ([3354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part011 : ℚ :=
  (79241985325 : ℚ) / 645370330816512

def SurrogateDiagonalTailChunk000Sub000Block080Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3354
    = surrogateDiagTailX0RatChunk000Sub000Block080Part011

theorem surrogateDiagonalTailChunk000Sub000Block080Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part011] using hcert

def TailChunk000Sub000Block080Part012SupportExplicit : Finset ℕ :=
  ([3355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part012 : ℚ :=
  (71869061 : ℚ) / 10370073600000

def SurrogateDiagonalTailChunk000Sub000Block080Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3355
    = surrogateDiagTailX0RatChunk000Sub000Block080Part012

theorem surrogateDiagonalTailChunk000Sub000Block080Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part012] using hcert

def TailChunk000Sub000Block080Part013SupportExplicit : Finset ℕ :=
  ([3358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part013 : ℚ :=
  (498376006675 : ℚ) / 15741552708845568

def SurrogateDiagonalTailChunk000Sub000Block080Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3358
    = surrogateDiagTailX0RatChunk000Sub000Block080Part013

theorem surrogateDiagonalTailChunk000Sub000Block080Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part013] using hcert

def TailChunk000Sub000Block080Part014SupportExplicit : Finset ℕ :=
  ([3359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part014 : ℚ :=
  (1410078052975 : ℚ) / 317943262324517448

def SurrogateDiagonalTailChunk000Sub000Block080Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3359
    = surrogateDiagTailX0RatChunk000Sub000Block080Part014

theorem surrogateDiagonalTailChunk000Sub000Block080Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part014] using hcert

def TailChunk000Sub000Block080Part015SupportExplicit : Finset ℕ :=
  ([3361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part015 : ℚ :=
  (56470308679 : ℚ) / 12748055917363200

def SurrogateDiagonalTailChunk000Sub000Block080Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3361
    = surrogateDiagTailX0RatChunk000Sub000Block080Part015

theorem surrogateDiagonalTailChunk000Sub000Block080Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part015] using hcert

def TailChunk000Sub000Block080Part016SupportExplicit : Finset ℕ :=
  ([3363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part016 : ℚ :=
  (363205844525 : ℚ) / 23763961523856384

def SurrogateDiagonalTailChunk000Sub000Block080Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3363
    = surrogateDiagTailX0RatChunk000Sub000Block080Part016

theorem surrogateDiagonalTailChunk000Sub000Block080Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part016] using hcert

def TailChunk000Sub000Block080Part017SupportExplicit : Finset ℕ :=
  ([3365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part017 : ℚ :=
  (1073952865075 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block080Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3365
    = surrogateDiagTailX0RatChunk000Sub000Block080Part017

theorem surrogateDiagonalTailChunk000Sub000Block080Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part017] using hcert

def TailChunk000Sub000Block080Part018SupportExplicit : Finset ℕ :=
  ([3367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part018 : ℚ :=
  (608200965775 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block080Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3367
    = surrogateDiagTailX0RatChunk000Sub000Block080Part018

theorem surrogateDiagonalTailChunk000Sub000Block080Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part018] using hcert

def TailChunk000Sub000Block080Part019SupportExplicit : Finset ℕ :=
  ([3369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part019 : ℚ :=
  (551480950675 : ℚ) / 63404235329643648

def SurrogateDiagonalTailChunk000Sub000Block080Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3369
    = surrogateDiagTailX0RatChunk000Sub000Block080Part019

theorem surrogateDiagonalTailChunk000Sub000Block080Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part019] using hcert

def TailChunk000Sub000Block080Part020SupportExplicit : Finset ℕ :=
  ([3370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part020 : ℚ :=
  (212346085625 : ℚ) / 4079377893556224

def SurrogateDiagonalTailChunk000Sub000Block080Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3370
    = surrogateDiagTailX0RatChunk000Sub000Block080Part020

theorem surrogateDiagonalTailChunk000Sub000Block080Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part020] using hcert

def TailChunk000Sub000Block080Part021SupportExplicit : Finset ℕ :=
  ([3371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part021 : ℚ :=
  (284091025 : ℚ) / 129004973445522

def SurrogateDiagonalTailChunk000Sub000Block080Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3371
    = surrogateDiagTailX0RatChunk000Sub000Block080Part021

theorem surrogateDiagonalTailChunk000Sub000Block080Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part021] using hcert

def TailChunk000Sub000Block080Part022SupportExplicit : Finset ℕ :=
  ([3373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part022 : ℚ :=
  (177767640625 : ℚ) / 80819680896198432

def SurrogateDiagonalTailChunk000Sub000Block080Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3373
    = surrogateDiagTailX0RatChunk000Sub000Block080Part022

theorem surrogateDiagonalTailChunk000Sub000Block080Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part022] using hcert

def TailChunk000Sub000Block080Part023SupportExplicit : Finset ℕ :=
  ([3374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part023 : ℚ :=
  (506175173 : ℚ) / 11946324787200

def SurrogateDiagonalTailChunk000Sub000Block080Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3374
    = surrogateDiagTailX0RatChunk000Sub000Block080Part023

theorem surrogateDiagonalTailChunk000Sub000Block080Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part023] using hcert

def TailChunk000Sub000Block080Part024SupportExplicit : Finset ℕ :=
  ([3377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block080Part024 : ℚ :=
  (360658697 : ℚ) / 116926053814656

def SurrogateDiagonalTailChunk000Sub000Block080Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3377
    = surrogateDiagTailX0RatChunk000Sub000Block080Part024

theorem surrogateDiagonalTailChunk000Sub000Block080Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block080Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block080Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block080Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block080Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block080Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block080Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block080HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block080Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block080Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block080Part000
    + surrogateDiagTailX0RatChunk000Sub000Block080Part001
    + surrogateDiagTailX0RatChunk000Sub000Block080Part002
    + surrogateDiagTailX0RatChunk000Sub000Block080Part003
    + surrogateDiagTailX0RatChunk000Sub000Block080Part004
    + surrogateDiagTailX0RatChunk000Sub000Block080Part005
    + surrogateDiagTailX0RatChunk000Sub000Block080Part006
    + surrogateDiagTailX0RatChunk000Sub000Block080Part007
    + surrogateDiagTailX0RatChunk000Sub000Block080Part008
    + surrogateDiagTailX0RatChunk000Sub000Block080Part009

def surrogateDiagonalTailChunk000Sub000Block080MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block080Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block080Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block080Part010
    + surrogateDiagTailX0RatChunk000Sub000Block080Part011
    + surrogateDiagTailX0RatChunk000Sub000Block080Part012
    + surrogateDiagTailX0RatChunk000Sub000Block080Part013
    + surrogateDiagTailX0RatChunk000Sub000Block080Part014
    + surrogateDiagTailX0RatChunk000Sub000Block080Part015
    + surrogateDiagTailX0RatChunk000Sub000Block080Part016
    + surrogateDiagTailX0RatChunk000Sub000Block080Part017
    + surrogateDiagTailX0RatChunk000Sub000Block080Part018
    + surrogateDiagTailX0RatChunk000Sub000Block080Part019

def surrogateDiagonalTailChunk000Sub000Block080TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block080Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block080Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block080Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block080Part020
    + surrogateDiagTailX0RatChunk000Sub000Block080Part021
    + surrogateDiagTailX0RatChunk000Sub000Block080Part022
    + surrogateDiagTailX0RatChunk000Sub000Block080Part023
    + surrogateDiagTailX0RatChunk000Sub000Block080Part024

def surrogateDiagonalTailChunk000Sub000Block080Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block080HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block080MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block080TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block080 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block080Part000
    + surrogateDiagTailX0RatChunk000Sub000Block080Part001
    + surrogateDiagTailX0RatChunk000Sub000Block080Part002
    + surrogateDiagTailX0RatChunk000Sub000Block080Part003
    + surrogateDiagTailX0RatChunk000Sub000Block080Part004
    + surrogateDiagTailX0RatChunk000Sub000Block080Part005
    + surrogateDiagTailX0RatChunk000Sub000Block080Part006
    + surrogateDiagTailX0RatChunk000Sub000Block080Part007
    + surrogateDiagTailX0RatChunk000Sub000Block080Part008
    + surrogateDiagTailX0RatChunk000Sub000Block080Part009
    + surrogateDiagTailX0RatChunk000Sub000Block080Part010
    + surrogateDiagTailX0RatChunk000Sub000Block080Part011
    + surrogateDiagTailX0RatChunk000Sub000Block080Part012
    + surrogateDiagTailX0RatChunk000Sub000Block080Part013
    + surrogateDiagTailX0RatChunk000Sub000Block080Part014
    + surrogateDiagTailX0RatChunk000Sub000Block080Part015
    + surrogateDiagTailX0RatChunk000Sub000Block080Part016
    + surrogateDiagTailX0RatChunk000Sub000Block080Part017
    + surrogateDiagTailX0RatChunk000Sub000Block080Part018
    + surrogateDiagTailX0RatChunk000Sub000Block080Part019
    + surrogateDiagTailX0RatChunk000Sub000Block080Part020
    + surrogateDiagTailX0RatChunk000Sub000Block080Part021
    + surrogateDiagTailX0RatChunk000Sub000Block080Part022
    + surrogateDiagTailX0RatChunk000Sub000Block080Part023
    + surrogateDiagTailX0RatChunk000Sub000Block080Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block080_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block080Head + surrogateDiagTailX0RatChunk000Sub000Block080Mid + surrogateDiagTailX0RatChunk000Sub000Block080Tail =
      surrogateDiagTailX0RatChunk000Sub000Block080 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block080Head surrogateDiagTailX0RatChunk000Sub000Block080Mid surrogateDiagTailX0RatChunk000Sub000Block080Tail surrogateDiagTailX0RatChunk000Sub000Block080
  ring

def SurrogateDiagonalTailChunk000Sub000Block080HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block080HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block080Head

def SurrogateDiagonalTailChunk000Sub000Block080MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block080MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block080Mid

def SurrogateDiagonalTailChunk000Sub000Block080TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block080TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block080Tail

theorem surrogateDiagonalTailChunk000Sub000Block080_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block080HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block080MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block080TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block080Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block080 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block080HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block080MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block080TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block080Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block080_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
