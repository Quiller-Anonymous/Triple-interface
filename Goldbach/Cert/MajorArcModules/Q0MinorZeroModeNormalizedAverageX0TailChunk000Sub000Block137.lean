import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [137,138). -/

/- Block 137 covers tail-support indices [3425,3450) and q from 5690 to 5727. -/

def TailChunk000Sub000Block137Part000SupportExplicit : Finset ℕ :=
  ([5690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part000 : ℚ :=
  (196949525275 : ℚ) / 16657130020012032

def SurrogateDiagonalTailChunk000Sub000Block137Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5690
    = surrogateDiagTailX0RatChunk000Sub000Block137Part000

theorem surrogateDiagonalTailChunk000Sub000Block137Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part000] using hcert

def TailChunk000Sub000Block137Part001SupportExplicit : Finset ℕ :=
  ([5691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part001 : ℚ :=
  (374857 : ℚ) / 91833004800

def SurrogateDiagonalTailChunk000Sub000Block137Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5691
    = surrogateDiagTailX0RatChunk000Sub000Block137Part001

theorem surrogateDiagonalTailChunk000Sub000Block137Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part001] using hcert

def TailChunk000Sub000Block137Part002SupportExplicit : Finset ℕ :=
  ([5693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part002 : ℚ :=
  (506410140625 : ℚ) / 656185203605121312

def SurrogateDiagonalTailChunk000Sub000Block137Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5693
    = surrogateDiagTailX0RatChunk000Sub000Block137Part002

theorem surrogateDiagonalTailChunk000Sub000Block137Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part002] using hcert

def TailChunk000Sub000Block137Part003SupportExplicit : Finset ℕ :=
  ([5694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part003 : ℚ :=
  (67433719775 : ℚ) / 2477189907873792

def SurrogateDiagonalTailChunk000Sub000Block137Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5694
    = surrogateDiagTailX0RatChunk000Sub000Block137Part003

theorem surrogateDiagonalTailChunk000Sub000Block137Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part003] using hcert

def TailChunk000Sub000Block137Part004SupportExplicit : Finset ℕ :=
  ([5695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part004 : ℚ :=
  (745075890575 : ℚ) / 398008641329823744

def SurrogateDiagonalTailChunk000Sub000Block137Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5695
    = surrogateDiagTailX0RatChunk000Sub000Block137Part004

theorem surrogateDiagonalTailChunk000Sub000Block137Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part004] using hcert

def TailChunk000Sub000Block137Part005SupportExplicit : Finset ℕ :=
  ([5698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part005 : ℚ :=
  (9876070141 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub000Block137Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5698
    = surrogateDiagTailX0RatChunk000Sub000Block137Part005

theorem surrogateDiagonalTailChunk000Sub000Block137Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part005] using hcert

def TailChunk000Sub000Block137Part006SupportExplicit : Finset ℕ :=
  ([5699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part006 : ℚ :=
  (39176943437 : ℚ) / 46431548260761600

def SurrogateDiagonalTailChunk000Sub000Block137Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5699
    = surrogateDiagTailX0RatChunk000Sub000Block137Part006

theorem surrogateDiagonalTailChunk000Sub000Block137Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part006] using hcert

def TailChunk000Sub000Block137Part007SupportExplicit : Finset ℕ :=
  ([5701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part007 : ℚ :=
  (32501401 : ℚ) / 42232448800800

def SurrogateDiagonalTailChunk000Sub000Block137Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5701
    = surrogateDiagTailX0RatChunk000Sub000Block137Part007

theorem surrogateDiagonalTailChunk000Sub000Block137Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part007] using hcert

def TailChunk000Sub000Block137Part008SupportExplicit : Finset ℕ :=
  ([5702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part008 : ℚ :=
  (40632876799 : ℚ) / 6598820125125000

def SurrogateDiagonalTailChunk000Sub000Block137Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5702
    = surrogateDiagTailX0RatChunk000Sub000Block137Part008

theorem surrogateDiagonalTailChunk000Sub000Block137Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part008] using hcert

def TailChunk000Sub000Block137Part009SupportExplicit : Finset ℕ :=
  ([5703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part009 : ℚ :=
  (22578607799 : ℚ) / 10427765136000000

def SurrogateDiagonalTailChunk000Sub000Block137Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5703
    = surrogateDiagTailX0RatChunk000Sub000Block137Part009

theorem surrogateDiagonalTailChunk000Sub000Block137Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part009] using hcert

def TailChunk000Sub000Block137Part010SupportExplicit : Finset ℕ :=
  ([5705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part010 : ℚ :=
  (1296930618475 : ℚ) / 571389011211091968

def SurrogateDiagonalTailChunk000Sub000Block137Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5705
    = surrogateDiagTailX0RatChunk000Sub000Block137Part010

theorem surrogateDiagonalTailChunk000Sub000Block137Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part010] using hcert

def TailChunk000Sub000Block137Part011SupportExplicit : Finset ℕ :=
  ([5707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part011 : ℚ :=
  (17246320775 : ℚ) / 17669510956832256

def SurrogateDiagonalTailChunk000Sub000Block137Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5707
    = surrogateDiagTailX0RatChunk000Sub000Block137Part011

theorem surrogateDiagonalTailChunk000Sub000Block137Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part011] using hcert

def TailChunk000Sub000Block137Part012SupportExplicit : Finset ℕ :=
  ([5709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part012 : ℚ :=
  (48554417017 : ℚ) / 14006209577779200

def SurrogateDiagonalTailChunk000Sub000Block137Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5709
    = surrogateDiagTailX0RatChunk000Sub000Block137Part012

theorem surrogateDiagonalTailChunk000Sub000Block137Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part012] using hcert

def TailChunk000Sub000Block137Part013SupportExplicit : Finset ℕ :=
  ([5710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part013 : ℚ :=
  (4886317831 : ℚ) / 675719180812800

def SurrogateDiagonalTailChunk000Sub000Block137Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5710
    = surrogateDiagTailX0RatChunk000Sub000Block137Part013

theorem surrogateDiagonalTailChunk000Sub000Block137Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part013] using hcert

def TailChunk000Sub000Block137Part014SupportExplicit : Finset ℕ :=
  ([5711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part014 : ℚ :=
  (815388025 : ℚ) / 1063239942277362

def SurrogateDiagonalTailChunk000Sub000Block137Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5711
    = surrogateDiagTailX0RatChunk000Sub000Block137Part014

theorem surrogateDiagonalTailChunk000Sub000Block137Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part014] using hcert

def TailChunk000Sub000Block137Part015SupportExplicit : Finset ℕ :=
  ([5713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part015 : ℚ :=
  (46406405475 : ℚ) / 54005001102639104

def SurrogateDiagonalTailChunk000Sub000Block137Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5713
    = surrogateDiagTailX0RatChunk000Sub000Block137Part015

theorem surrogateDiagonalTailChunk000Sub000Block137Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part015] using hcert

def TailChunk000Sub000Block137Part016SupportExplicit : Finset ℕ :=
  ([5714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part016 : ℚ :=
  (127538265625 : ℚ) / 41591030401331712

def SurrogateDiagonalTailChunk000Sub000Block137Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5714
    = surrogateDiagTailX0RatChunk000Sub000Block137Part016

theorem surrogateDiagonalTailChunk000Sub000Block137Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part016] using hcert

def TailChunk000Sub000Block137Part017SupportExplicit : Finset ℕ :=
  ([5717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part017 : ℚ :=
  (510688890625 : ℚ) / 667322469115221792

def SurrogateDiagonalTailChunk000Sub000Block137Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5717
    = surrogateDiagTailX0RatChunk000Sub000Block137Part017

theorem surrogateDiagonalTailChunk000Sub000Block137Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part017] using hcert

def TailChunk000Sub000Block137Part018SupportExplicit : Finset ℕ :=
  ([5718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part018 : ℚ :=
  (623821826575 : ℚ) / 32862048712163328

def SurrogateDiagonalTailChunk000Sub000Block137Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5718
    = surrogateDiagTailX0RatChunk000Sub000Block137Part018

theorem surrogateDiagonalTailChunk000Sub000Block137Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part018] using hcert

def TailChunk000Sub000Block137Part019SupportExplicit : Finset ℕ :=
  ([5719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part019 : ℚ :=
  (178116292625 : ℚ) / 117618742791309312

def SurrogateDiagonalTailChunk000Sub000Block137Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5719
    = surrogateDiagTailX0RatChunk000Sub000Block137Part019

theorem surrogateDiagonalTailChunk000Sub000Block137Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part019] using hcert

def TailChunk000Sub000Block137Part020SupportExplicit : Finset ℕ :=
  ([5721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part020 : ℚ :=
  (35502118175 : ℚ) / 16500171127970724

def SurrogateDiagonalTailChunk000Sub000Block137Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5721
    = surrogateDiagTailX0RatChunk000Sub000Block137Part020

theorem surrogateDiagonalTailChunk000Sub000Block137Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part020] using hcert

def TailChunk000Sub000Block137Part021SupportExplicit : Finset ℕ :=
  ([5722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part021 : ℚ :=
  (40918419679 : ℚ) / 6691923733123200

def SurrogateDiagonalTailChunk000Sub000Block137Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5722
    = surrogateDiagTailX0RatChunk000Sub000Block137Part021

theorem surrogateDiagonalTailChunk000Sub000Block137Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part021] using hcert

def TailChunk000Sub000Block137Part022SupportExplicit : Finset ℕ :=
  ([5723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part022 : ℚ :=
  (496349133925 : ℚ) / 600846829640220672

def SurrogateDiagonalTailChunk000Sub000Block137Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5723
    = surrogateDiagTailX0RatChunk000Sub000Block137Part022

theorem surrogateDiagonalTailChunk000Sub000Block137Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part022] using hcert

def TailChunk000Sub000Block137Part023SupportExplicit : Finset ℕ :=
  ([5726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part023 : ℚ :=
  (427579943225 : ℚ) / 44899604664827904

def SurrogateDiagonalTailChunk000Sub000Block137Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5726
    = surrogateDiagTailX0RatChunk000Sub000Block137Part023

theorem surrogateDiagonalTailChunk000Sub000Block137Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part023] using hcert

def TailChunk000Sub000Block137Part024SupportExplicit : Finset ℕ :=
  ([5727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block137Part024 : ℚ :=
  (1282078545325 : ℚ) / 423733669830248448

def SurrogateDiagonalTailChunk000Sub000Block137Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5727
    = surrogateDiagTailX0RatChunk000Sub000Block137Part024

theorem surrogateDiagonalTailChunk000Sub000Block137Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block137Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block137Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block137Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block137Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block137Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block137Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block137HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block137Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block137Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block137Part000
    + surrogateDiagTailX0RatChunk000Sub000Block137Part001
    + surrogateDiagTailX0RatChunk000Sub000Block137Part002
    + surrogateDiagTailX0RatChunk000Sub000Block137Part003
    + surrogateDiagTailX0RatChunk000Sub000Block137Part004
    + surrogateDiagTailX0RatChunk000Sub000Block137Part005
    + surrogateDiagTailX0RatChunk000Sub000Block137Part006
    + surrogateDiagTailX0RatChunk000Sub000Block137Part007
    + surrogateDiagTailX0RatChunk000Sub000Block137Part008
    + surrogateDiagTailX0RatChunk000Sub000Block137Part009

def surrogateDiagonalTailChunk000Sub000Block137MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block137Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block137Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block137Part010
    + surrogateDiagTailX0RatChunk000Sub000Block137Part011
    + surrogateDiagTailX0RatChunk000Sub000Block137Part012
    + surrogateDiagTailX0RatChunk000Sub000Block137Part013
    + surrogateDiagTailX0RatChunk000Sub000Block137Part014
    + surrogateDiagTailX0RatChunk000Sub000Block137Part015
    + surrogateDiagTailX0RatChunk000Sub000Block137Part016
    + surrogateDiagTailX0RatChunk000Sub000Block137Part017
    + surrogateDiagTailX0RatChunk000Sub000Block137Part018
    + surrogateDiagTailX0RatChunk000Sub000Block137Part019

def surrogateDiagonalTailChunk000Sub000Block137TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block137Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block137Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block137Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block137Part020
    + surrogateDiagTailX0RatChunk000Sub000Block137Part021
    + surrogateDiagTailX0RatChunk000Sub000Block137Part022
    + surrogateDiagTailX0RatChunk000Sub000Block137Part023
    + surrogateDiagTailX0RatChunk000Sub000Block137Part024

def surrogateDiagonalTailChunk000Sub000Block137Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block137HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block137MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block137TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block137 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block137Part000
    + surrogateDiagTailX0RatChunk000Sub000Block137Part001
    + surrogateDiagTailX0RatChunk000Sub000Block137Part002
    + surrogateDiagTailX0RatChunk000Sub000Block137Part003
    + surrogateDiagTailX0RatChunk000Sub000Block137Part004
    + surrogateDiagTailX0RatChunk000Sub000Block137Part005
    + surrogateDiagTailX0RatChunk000Sub000Block137Part006
    + surrogateDiagTailX0RatChunk000Sub000Block137Part007
    + surrogateDiagTailX0RatChunk000Sub000Block137Part008
    + surrogateDiagTailX0RatChunk000Sub000Block137Part009
    + surrogateDiagTailX0RatChunk000Sub000Block137Part010
    + surrogateDiagTailX0RatChunk000Sub000Block137Part011
    + surrogateDiagTailX0RatChunk000Sub000Block137Part012
    + surrogateDiagTailX0RatChunk000Sub000Block137Part013
    + surrogateDiagTailX0RatChunk000Sub000Block137Part014
    + surrogateDiagTailX0RatChunk000Sub000Block137Part015
    + surrogateDiagTailX0RatChunk000Sub000Block137Part016
    + surrogateDiagTailX0RatChunk000Sub000Block137Part017
    + surrogateDiagTailX0RatChunk000Sub000Block137Part018
    + surrogateDiagTailX0RatChunk000Sub000Block137Part019
    + surrogateDiagTailX0RatChunk000Sub000Block137Part020
    + surrogateDiagTailX0RatChunk000Sub000Block137Part021
    + surrogateDiagTailX0RatChunk000Sub000Block137Part022
    + surrogateDiagTailX0RatChunk000Sub000Block137Part023
    + surrogateDiagTailX0RatChunk000Sub000Block137Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block137_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block137Head + surrogateDiagTailX0RatChunk000Sub000Block137Mid + surrogateDiagTailX0RatChunk000Sub000Block137Tail =
      surrogateDiagTailX0RatChunk000Sub000Block137 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block137Head surrogateDiagTailX0RatChunk000Sub000Block137Mid surrogateDiagTailX0RatChunk000Sub000Block137Tail surrogateDiagTailX0RatChunk000Sub000Block137
  ring

def SurrogateDiagonalTailChunk000Sub000Block137HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block137HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block137Head

def SurrogateDiagonalTailChunk000Sub000Block137MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block137MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block137Mid

def SurrogateDiagonalTailChunk000Sub000Block137TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block137TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block137Tail

theorem surrogateDiagonalTailChunk000Sub000Block137_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block137HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block137MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block137TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block137Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block137 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block137HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block137MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block137TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block137Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block137_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
