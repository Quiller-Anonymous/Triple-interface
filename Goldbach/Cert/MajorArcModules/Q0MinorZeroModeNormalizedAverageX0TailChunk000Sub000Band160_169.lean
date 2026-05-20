import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [160,170). -/

/-- Block 160 covers tail-support indices [4000,4025) and q from 6629 to 6670. -/

def TailChunk000Sub000Block160Part000SupportExplicit : Finset ℕ :=
  ([6629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part000 : ℚ :=
  (2295541862575 : ℚ) / 2595352823232732288

def SurrogateDiagonalTailChunk000Sub000Block160Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6629
    = surrogateDiagTailX0RatChunk000Sub000Block160Part000

theorem surrogateDiagonalTailChunk000Sub000Block160Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part000] using hcert

def TailChunk000Sub000Block160Part001SupportExplicit : Finset ℕ :=
  ([6630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part001 : ℚ :=
  (90662053225 : ℚ) / 2319746196307968

def SurrogateDiagonalTailChunk000Sub000Block160Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6630
    = surrogateDiagTailX0RatChunk000Sub000Block160Part001

theorem surrogateDiagonalTailChunk000Sub000Block160Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part001] using hcert

def TailChunk000Sub000Block160Part002SupportExplicit : Finset ℕ :=
  ([6631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part002 : ℚ :=
  (142045935875 : ℚ) / 213875653714707456

def SurrogateDiagonalTailChunk000Sub000Block160Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6631
    = surrogateDiagTailX0RatChunk000Sub000Block160Part002

theorem surrogateDiagonalTailChunk000Sub000Block160Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part002] using hcert

def TailChunk000Sub000Block160Part003SupportExplicit : Finset ℕ :=
  ([6634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part003 : ℚ :=
  (10440984509 : ℚ) / 2045621717735040

def SurrogateDiagonalTailChunk000Sub000Block160Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6634
    = surrogateDiagTailX0RatChunk000Sub000Block160Part003

theorem surrogateDiagonalTailChunk000Sub000Block160Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part003] using hcert

def TailChunk000Sub000Block160Part004SupportExplicit : Finset ℕ :=
  ([6635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part004 : ℚ :=
  (174133210325 : ℚ) / 164914815950636544

def SurrogateDiagonalTailChunk000Sub000Block160Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6635
    = surrogateDiagTailX0RatChunk000Sub000Block160Part004

theorem surrogateDiagonalTailChunk000Sub000Block160Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part004] using hcert

def TailChunk000Sub000Block160Part005SupportExplicit : Finset ℕ :=
  ([6637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part005 : ℚ :=
  (688277640625 : ℚ) / 1212250514096254752

def SurrogateDiagonalTailChunk000Sub000Block160Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6637
    = surrogateDiagTailX0RatChunk000Sub000Block160Part005

theorem surrogateDiagonalTailChunk000Sub000Block160Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part005] using hcert

def TailChunk000Sub000Block160Part006SupportExplicit : Finset ℕ :=
  ([6638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part006 : ℚ :=
  (1376694730975 : ℚ) / 303062628524063688

def SurrogateDiagonalTailChunk000Sub000Block160Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6638
    = surrogateDiagTailX0RatChunk000Sub000Block160Part006

theorem surrogateDiagonalTailChunk000Sub000Block160Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part006] using hcert

def TailChunk000Sub000Block160Part007SupportExplicit : Finset ℕ :=
  ([6639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part007 : ℚ :=
  (535125 : ℚ) / 279194180608

def SurrogateDiagonalTailChunk000Sub000Block160Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6639
    = surrogateDiagTailX0RatChunk000Sub000Block160Part007

theorem surrogateDiagonalTailChunk000Sub000Block160Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part007] using hcert

def TailChunk000Sub000Block160Part008SupportExplicit : Finset ℕ :=
  ([6641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part008 : ℚ :=
  (656154170425 : ℚ) / 1038337122004180992

def SurrogateDiagonalTailChunk000Sub000Block160Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6641
    = surrogateDiagTailX0RatChunk000Sub000Block160Part008

theorem surrogateDiagonalTailChunk000Sub000Block160Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part008] using hcert

def TailChunk000Sub000Block160Part009SupportExplicit : Finset ℕ :=
  ([6643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part009 : ℚ :=
  (514393733575 : ℚ) / 451467860709998592

def SurrogateDiagonalTailChunk000Sub000Block160Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6643
    = surrogateDiagTailX0RatChunk000Sub000Block160Part009

theorem surrogateDiagonalTailChunk000Sub000Block160Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part009] using hcert

def TailChunk000Sub000Block160Part010SupportExplicit : Finset ℕ :=
  ([6645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part010 : ℚ :=
  (102162664575 : ℚ) / 65151532227411968

def SurrogateDiagonalTailChunk000Sub000Block160Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6645
    = surrogateDiagTailX0RatChunk000Sub000Block160Part010

theorem surrogateDiagonalTailChunk000Sub000Block160Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part010] using hcert

def TailChunk000Sub000Block160Part011SupportExplicit : Finset ℕ :=
  ([6646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part011 : ℚ :=
  (172536390625 : ℚ) / 76131674132578482

def SurrogateDiagonalTailChunk000Sub000Block160Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6646
    = surrogateDiagTailX0RatChunk000Sub000Block160Part011

theorem surrogateDiagonalTailChunk000Sub000Block160Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part011] using hcert

def TailChunk000Sub000Block160Part012SupportExplicit : Finset ℕ :=
  ([6649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part012 : ℚ :=
  (64980803 : ℚ) / 5511082284057600

def SurrogateDiagonalTailChunk000Sub000Block160Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6649
    = surrogateDiagTailX0RatChunk000Sub000Block160Part012

theorem surrogateDiagonalTailChunk000Sub000Block160Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part012] using hcert

def TailChunk000Sub000Block160Part013SupportExplicit : Finset ℕ :=
  ([6653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block160Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6653
    = surrogateDiagTailX0RatChunk000Sub000Block160Part013

theorem surrogateDiagonalTailChunk000Sub000Block160Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part013] using hcert

def TailChunk000Sub000Block160Part014SupportExplicit : Finset ℕ :=
  ([6654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part014 : ℚ :=
  (614518022275 : ℚ) / 60298413147015168

def SurrogateDiagonalTailChunk000Sub000Block160Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6654
    = surrogateDiagTailX0RatChunk000Sub000Block160Part014

theorem surrogateDiagonalTailChunk000Sub000Block160Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part014] using hcert

def TailChunk000Sub000Block160Part015SupportExplicit : Finset ℕ :=
  ([6657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part015 : ℚ :=
  (652615371475 : ℚ) / 517011464570830848

def SurrogateDiagonalTailChunk000Sub000Block160Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6657
    = surrogateDiagTailX0RatChunk000Sub000Block160Part015

theorem surrogateDiagonalTailChunk000Sub000Block160Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part015] using hcert

def TailChunk000Sub000Block160Part016SupportExplicit : Finset ℕ :=
  ([6658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part016 : ℚ :=
  (173160015625 : ℚ) / 76683184158277632

def SurrogateDiagonalTailChunk000Sub000Block160Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6658
    = surrogateDiagTailX0RatChunk000Sub000Block160Part016

theorem surrogateDiagonalTailChunk000Sub000Block160Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part016] using hcert

def TailChunk000Sub000Block160Part017SupportExplicit : Finset ℕ :=
  ([6659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block160Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6659
    = surrogateDiagTailX0RatChunk000Sub000Block160Part017

theorem surrogateDiagonalTailChunk000Sub000Block160Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part017] using hcert

def TailChunk000Sub000Block160Part018SupportExplicit : Finset ℕ :=
  ([6661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block160Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6661
    = surrogateDiagTailX0RatChunk000Sub000Block160Part018

theorem surrogateDiagonalTailChunk000Sub000Block160Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part018] using hcert

def TailChunk000Sub000Block160Part019SupportExplicit : Finset ℕ :=
  ([6662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part019 : ℚ :=
  (277389025 : ℚ) / 122988295950642

def SurrogateDiagonalTailChunk000Sub000Block160Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6662
    = surrogateDiagTailX0RatChunk000Sub000Block160Part019

theorem surrogateDiagonalTailChunk000Sub000Block160Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part019] using hcert

def TailChunk000Sub000Block160Part020SupportExplicit : Finset ℕ :=
  ([6663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part020 : ℚ :=
  (12331033859 : ℚ) / 19435187508249600

def SurrogateDiagonalTailChunk000Sub000Block160Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6663
    = surrogateDiagTailX0RatChunk000Sub000Block160Part020

theorem surrogateDiagonalTailChunk000Sub000Block160Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part020] using hcert

def TailChunk000Sub000Block160Part021SupportExplicit : Finset ℕ :=
  ([6665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part021 : ℚ :=
  (7721324747 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub000Block160Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6665
    = surrogateDiagTailX0RatChunk000Sub000Block160Part021

theorem surrogateDiagonalTailChunk000Sub000Block160Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part021] using hcert

def TailChunk000Sub000Block160Part022SupportExplicit : Finset ℕ :=
  ([6666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part022 : ℚ :=
  (40054163 : ℚ) / 3200640000000

def SurrogateDiagonalTailChunk000Sub000Block160Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6666
    = surrogateDiagTailX0RatChunk000Sub000Block160Part022

theorem surrogateDiagonalTailChunk000Sub000Block160Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part022] using hcert

def TailChunk000Sub000Block160Part023SupportExplicit : Finset ℕ :=
  ([6667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part023 : ℚ :=
  (96083740525 : ℚ) / 159020418647064576

def SurrogateDiagonalTailChunk000Sub000Block160Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6667
    = surrogateDiagTailX0RatChunk000Sub000Block160Part023

theorem surrogateDiagonalTailChunk000Sub000Block160Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part023] using hcert

def TailChunk000Sub000Block160Part024SupportExplicit : Finset ℕ :=
  ([6670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block160Part024 : ℚ :=
  (959469535825 : ℚ) / 92170018116599808

def SurrogateDiagonalTailChunk000Sub000Block160Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6670
    = surrogateDiagTailX0RatChunk000Sub000Block160Part024

theorem surrogateDiagonalTailChunk000Sub000Block160Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block160Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block160Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block160Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block160Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block160Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block160Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block160HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block160Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block160Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block160Part000
    + surrogateDiagTailX0RatChunk000Sub000Block160Part001
    + surrogateDiagTailX0RatChunk000Sub000Block160Part002
    + surrogateDiagTailX0RatChunk000Sub000Block160Part003
    + surrogateDiagTailX0RatChunk000Sub000Block160Part004
    + surrogateDiagTailX0RatChunk000Sub000Block160Part005
    + surrogateDiagTailX0RatChunk000Sub000Block160Part006
    + surrogateDiagTailX0RatChunk000Sub000Block160Part007
    + surrogateDiagTailX0RatChunk000Sub000Block160Part008
    + surrogateDiagTailX0RatChunk000Sub000Block160Part009

def surrogateDiagonalTailChunk000Sub000Block160MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block160Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block160Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block160Part010
    + surrogateDiagTailX0RatChunk000Sub000Block160Part011
    + surrogateDiagTailX0RatChunk000Sub000Block160Part012
    + surrogateDiagTailX0RatChunk000Sub000Block160Part013
    + surrogateDiagTailX0RatChunk000Sub000Block160Part014
    + surrogateDiagTailX0RatChunk000Sub000Block160Part015
    + surrogateDiagTailX0RatChunk000Sub000Block160Part016
    + surrogateDiagTailX0RatChunk000Sub000Block160Part017
    + surrogateDiagTailX0RatChunk000Sub000Block160Part018
    + surrogateDiagTailX0RatChunk000Sub000Block160Part019

def surrogateDiagonalTailChunk000Sub000Block160TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block160Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block160Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block160Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block160Part020
    + surrogateDiagTailX0RatChunk000Sub000Block160Part021
    + surrogateDiagTailX0RatChunk000Sub000Block160Part022
    + surrogateDiagTailX0RatChunk000Sub000Block160Part023
    + surrogateDiagTailX0RatChunk000Sub000Block160Part024

def surrogateDiagonalTailChunk000Sub000Block160Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block160HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block160MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block160TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block160 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block160Part000
    + surrogateDiagTailX0RatChunk000Sub000Block160Part001
    + surrogateDiagTailX0RatChunk000Sub000Block160Part002
    + surrogateDiagTailX0RatChunk000Sub000Block160Part003
    + surrogateDiagTailX0RatChunk000Sub000Block160Part004
    + surrogateDiagTailX0RatChunk000Sub000Block160Part005
    + surrogateDiagTailX0RatChunk000Sub000Block160Part006
    + surrogateDiagTailX0RatChunk000Sub000Block160Part007
    + surrogateDiagTailX0RatChunk000Sub000Block160Part008
    + surrogateDiagTailX0RatChunk000Sub000Block160Part009
    + surrogateDiagTailX0RatChunk000Sub000Block160Part010
    + surrogateDiagTailX0RatChunk000Sub000Block160Part011
    + surrogateDiagTailX0RatChunk000Sub000Block160Part012
    + surrogateDiagTailX0RatChunk000Sub000Block160Part013
    + surrogateDiagTailX0RatChunk000Sub000Block160Part014
    + surrogateDiagTailX0RatChunk000Sub000Block160Part015
    + surrogateDiagTailX0RatChunk000Sub000Block160Part016
    + surrogateDiagTailX0RatChunk000Sub000Block160Part017
    + surrogateDiagTailX0RatChunk000Sub000Block160Part018
    + surrogateDiagTailX0RatChunk000Sub000Block160Part019
    + surrogateDiagTailX0RatChunk000Sub000Block160Part020
    + surrogateDiagTailX0RatChunk000Sub000Block160Part021
    + surrogateDiagTailX0RatChunk000Sub000Block160Part022
    + surrogateDiagTailX0RatChunk000Sub000Block160Part023
    + surrogateDiagTailX0RatChunk000Sub000Block160Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block160_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block160Head + surrogateDiagTailX0RatChunk000Sub000Block160Mid + surrogateDiagTailX0RatChunk000Sub000Block160Tail =
      surrogateDiagTailX0RatChunk000Sub000Block160 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block160Head surrogateDiagTailX0RatChunk000Sub000Block160Mid surrogateDiagTailX0RatChunk000Sub000Block160Tail surrogateDiagTailX0RatChunk000Sub000Block160
  ring

def SurrogateDiagonalTailChunk000Sub000Block160HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block160HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block160Head

def SurrogateDiagonalTailChunk000Sub000Block160MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block160MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block160Mid

def SurrogateDiagonalTailChunk000Sub000Block160TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block160TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block160Tail

theorem surrogateDiagonalTailChunk000Sub000Block160_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block160HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block160MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block160TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block160Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block160 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block160HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block160MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block160TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block160Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block160_eq_head_add_mid_add_tail

/-- Block 161 covers tail-support indices [4025,4050) and q from 6671 to 6709. -/

def TailChunk000Sub000Block161Part000SupportExplicit : Finset ℕ :=
  ([6671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part000 : ℚ :=
  (133414112375 : ℚ) / 156577996805013504

def SurrogateDiagonalTailChunk000Sub000Block161Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6671
    = surrogateDiagTailX0RatChunk000Sub000Block161Part000

theorem surrogateDiagonalTailChunk000Sub000Block161Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part000] using hcert

def TailChunk000Sub000Block161Part001SupportExplicit : Finset ℕ :=
  ([6673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part001 : ℚ :=
  (695764515625 : ℚ) / 1238770966440517632

def SurrogateDiagonalTailChunk000Sub000Block161Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6673
    = surrogateDiagTailX0RatChunk000Sub000Block161Part001

theorem surrogateDiagonalTailChunk000Sub000Block161Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part001] using hcert

def TailChunk000Sub000Block161Part002SupportExplicit : Finset ℕ :=
  ([6674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part002 : ℚ :=
  (53246390581 : ℚ) / 10752521930371200

def SurrogateDiagonalTailChunk000Sub000Block161Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6674
    = surrogateDiagTailX0RatChunk000Sub000Block161Part002

theorem surrogateDiagonalTailChunk000Sub000Block161Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part002] using hcert

def TailChunk000Sub000Block161Part003SupportExplicit : Finset ℕ :=
  ([6677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part003 : ℚ :=
  (98378498851 : ℚ) / 134889252151939200

def SurrogateDiagonalTailChunk000Sub000Block161Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6677
    = surrogateDiagTailX0RatChunk000Sub000Block161Part003

theorem surrogateDiagonalTailChunk000Sub000Block161Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part003] using hcert

def TailChunk000Sub000Block161Part004SupportExplicit : Finset ℕ :=
  ([6679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part004 : ℚ :=
  (697016265625 : ℚ) / 1243232991521338482

def SurrogateDiagonalTailChunk000Sub000Block161Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6679
    = surrogateDiagTailX0RatChunk000Sub000Block161Part004

theorem surrogateDiagonalTailChunk000Sub000Block161Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part004] using hcert

def TailChunk000Sub000Block161Part005SupportExplicit : Finset ℕ :=
  ([6681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part005 : ℚ :=
  (28700056643 : ℚ) / 14977184405913600

def SurrogateDiagonalTailChunk000Sub000Block161Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6681
    = surrogateDiagTailX0RatChunk000Sub000Block161Part005

theorem surrogateDiagonalTailChunk000Sub000Block161Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part005] using hcert

def TailChunk000Sub000Block161Part006SupportExplicit : Finset ℕ :=
  ([6682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part006 : ℚ :=
  (1253224765075 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub000Block161Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6682
    = surrogateDiagTailX0RatChunk000Sub000Block161Part006

theorem surrogateDiagonalTailChunk000Sub000Block161Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part006] using hcert

def TailChunk000Sub000Block161Part007SupportExplicit : Finset ℕ :=
  ([6683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part007 : ℚ :=
  (8955048647 : ℚ) / 14696219424153600

def SurrogateDiagonalTailChunk000Sub000Block161Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6683
    = surrogateDiagTailX0RatChunk000Sub000Block161Part007

theorem surrogateDiagonalTailChunk000Sub000Block161Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part007] using hcert

def TailChunk000Sub000Block161Part008SupportExplicit : Finset ℕ :=
  ([6685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part008 : ℚ :=
  (13888502129 : ℚ) / 8649205514403840

def SurrogateDiagonalTailChunk000Sub000Block161Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6685
    = surrogateDiagTailX0RatChunk000Sub000Block161Part008

theorem surrogateDiagonalTailChunk000Sub000Block161Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part008] using hcert

def TailChunk000Sub000Block161Part009SupportExplicit : Finset ℕ :=
  ([6686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part009 : ℚ :=
  (1396676733775 : ℚ) / 311926764961656648

def SurrogateDiagonalTailChunk000Sub000Block161Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6686
    = surrogateDiagTailX0RatChunk000Sub000Block161Part009

theorem surrogateDiagonalTailChunk000Sub000Block161Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part009] using hcert

def TailChunk000Sub000Block161Part010SupportExplicit : Finset ℕ :=
  ([6689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part010 : ℚ :=
  (699105015625 : ℚ) / 1250696473445793792

def SurrogateDiagonalTailChunk000Sub000Block161Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6689
    = surrogateDiagTailX0RatChunk000Sub000Block161Part010

theorem surrogateDiagonalTailChunk000Sub000Block161Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part010] using hcert

def TailChunk000Sub000Block161Part011SupportExplicit : Finset ℕ :=
  ([6690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part011 : ℚ :=
  (152816608175 : ℚ) / 8292346670186496

def SurrogateDiagonalTailChunk000Sub000Block161Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6690
    = surrogateDiagTailX0RatChunk000Sub000Block161Part011

theorem surrogateDiagonalTailChunk000Sub000Block161Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part011] using hcert

def TailChunk000Sub000Block161Part012SupportExplicit : Finset ℕ :=
  ([6691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part012 : ℚ :=
  (1119237025 : ℚ) / 2003509108907442

def SurrogateDiagonalTailChunk000Sub000Block161Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6691
    = surrogateDiagTailX0RatChunk000Sub000Block161Part012

theorem surrogateDiagonalTailChunk000Sub000Block161Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part012] using hcert

def TailChunk000Sub000Block161Part013SupportExplicit : Finset ℕ :=
  ([6693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part013 : ℚ :=
  (1464130628875 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub000Block161Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6693
    = surrogateDiagTailX0RatChunk000Sub000Block161Part013

theorem surrogateDiagonalTailChunk000Sub000Block161Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part013] using hcert

def TailChunk000Sub000Block161Part014SupportExplicit : Finset ℕ :=
  ([6694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part014 : ℚ :=
  (175037640625 : ℚ) / 78355703477504082

def SurrogateDiagonalTailChunk000Sub000Block161Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6694
    = surrogateDiagTailX0RatChunk000Sub000Block161Part014

theorem surrogateDiagonalTailChunk000Sub000Block161Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part014] using hcert

def TailChunk000Sub000Block161Part015SupportExplicit : Finset ℕ :=
  ([6695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part015 : ℚ :=
  (106148734175 : ℚ) / 79821519404138496

def SurrogateDiagonalTailChunk000Sub000Block161Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6695
    = surrogateDiagTailX0RatChunk000Sub000Block161Part015

theorem surrogateDiagonalTailChunk000Sub000Block161Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part015] using hcert

def TailChunk000Sub000Block161Part016SupportExplicit : Finset ℕ :=
  ([6697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part016 : ℚ :=
  (3986275657 : ℚ) / 6531653077401600

def SurrogateDiagonalTailChunk000Sub000Block161Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6697
    = surrogateDiagTailX0RatChunk000Sub000Block161Part016

theorem surrogateDiagonalTailChunk000Sub000Block161Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part016] using hcert

def TailChunk000Sub000Block161Part017SupportExplicit : Finset ℕ :=
  ([6698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part017 : ℚ :=
  (677365210525 : ℚ) / 241841637590827008

def SurrogateDiagonalTailChunk000Sub000Block161Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6698
    = surrogateDiagTailX0RatChunk000Sub000Block161Part017

theorem surrogateDiagonalTailChunk000Sub000Block161Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part017] using hcert

def TailChunk000Sub000Block161Part018SupportExplicit : Finset ℕ :=
  ([6699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part018 : ℚ :=
  (26092319879 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub000Block161Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6699
    = surrogateDiagTailX0RatChunk000Sub000Block161Part018

theorem surrogateDiagonalTailChunk000Sub000Block161Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part018] using hcert

def TailChunk000Sub000Block161Part019SupportExplicit : Finset ℕ :=
  ([6701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part019 : ℚ :=
  (44903401 : ℚ) / 80620604896800

def SurrogateDiagonalTailChunk000Sub000Block161Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6701
    = surrogateDiagTailX0RatChunk000Sub000Block161Part019

theorem surrogateDiagonalTailChunk000Sub000Block161Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part019] using hcert

def TailChunk000Sub000Block161Part020SupportExplicit : Finset ℕ :=
  ([6702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part020 : ℚ :=
  (623414911075 : ℚ) / 62058835202623488

def SurrogateDiagonalTailChunk000Sub000Block161Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6702
    = surrogateDiagTailX0RatChunk000Sub000Block161Part020

theorem surrogateDiagonalTailChunk000Sub000Block161Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part020] using hcert

def TailChunk000Sub000Block161Part021SupportExplicit : Finset ℕ :=
  ([6703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part021 : ℚ :=
  (702034515625 : ℚ) / 1261201740894206802

def SurrogateDiagonalTailChunk000Sub000Block161Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6703
    = surrogateDiagTailX0RatChunk000Sub000Block161Part021

theorem surrogateDiagonalTailChunk000Sub000Block161Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part021] using hcert

def TailChunk000Sub000Block161Part022SupportExplicit : Finset ℕ :=
  ([6706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part022 : ℚ :=
  (164712267625 : ℚ) / 42294457187357472

def SurrogateDiagonalTailChunk000Sub000Block161Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6706
    = surrogateDiagTailX0RatChunk000Sub000Block161Part022

theorem surrogateDiagonalTailChunk000Sub000Block161Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part022] using hcert

def TailChunk000Sub000Block161Part023SupportExplicit : Finset ℕ :=
  ([6707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part023 : ℚ :=
  (1307906380625 : ℚ) / 2014918746732232704

def SurrogateDiagonalTailChunk000Sub000Block161Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6707
    = surrogateDiagTailX0RatChunk000Sub000Block161Part023

theorem surrogateDiagonalTailChunk000Sub000Block161Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part023] using hcert

def TailChunk000Sub000Block161Part024SupportExplicit : Finset ℕ :=
  ([6709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block161Part024 : ℚ :=
  (703291890625 : ℚ) / 1265724198899495712

def SurrogateDiagonalTailChunk000Sub000Block161Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6709
    = surrogateDiagTailX0RatChunk000Sub000Block161Part024

theorem surrogateDiagonalTailChunk000Sub000Block161Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block161Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block161Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block161Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block161Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block161Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block161Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block161HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block161Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block161Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block161Part000
    + surrogateDiagTailX0RatChunk000Sub000Block161Part001
    + surrogateDiagTailX0RatChunk000Sub000Block161Part002
    + surrogateDiagTailX0RatChunk000Sub000Block161Part003
    + surrogateDiagTailX0RatChunk000Sub000Block161Part004
    + surrogateDiagTailX0RatChunk000Sub000Block161Part005
    + surrogateDiagTailX0RatChunk000Sub000Block161Part006
    + surrogateDiagTailX0RatChunk000Sub000Block161Part007
    + surrogateDiagTailX0RatChunk000Sub000Block161Part008
    + surrogateDiagTailX0RatChunk000Sub000Block161Part009

def surrogateDiagonalTailChunk000Sub000Block161MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block161Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block161Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block161Part010
    + surrogateDiagTailX0RatChunk000Sub000Block161Part011
    + surrogateDiagTailX0RatChunk000Sub000Block161Part012
    + surrogateDiagTailX0RatChunk000Sub000Block161Part013
    + surrogateDiagTailX0RatChunk000Sub000Block161Part014
    + surrogateDiagTailX0RatChunk000Sub000Block161Part015
    + surrogateDiagTailX0RatChunk000Sub000Block161Part016
    + surrogateDiagTailX0RatChunk000Sub000Block161Part017
    + surrogateDiagTailX0RatChunk000Sub000Block161Part018
    + surrogateDiagTailX0RatChunk000Sub000Block161Part019

def surrogateDiagonalTailChunk000Sub000Block161TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block161Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block161Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block161Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block161Part020
    + surrogateDiagTailX0RatChunk000Sub000Block161Part021
    + surrogateDiagTailX0RatChunk000Sub000Block161Part022
    + surrogateDiagTailX0RatChunk000Sub000Block161Part023
    + surrogateDiagTailX0RatChunk000Sub000Block161Part024

def surrogateDiagonalTailChunk000Sub000Block161Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block161HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block161MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block161TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block161 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block161Part000
    + surrogateDiagTailX0RatChunk000Sub000Block161Part001
    + surrogateDiagTailX0RatChunk000Sub000Block161Part002
    + surrogateDiagTailX0RatChunk000Sub000Block161Part003
    + surrogateDiagTailX0RatChunk000Sub000Block161Part004
    + surrogateDiagTailX0RatChunk000Sub000Block161Part005
    + surrogateDiagTailX0RatChunk000Sub000Block161Part006
    + surrogateDiagTailX0RatChunk000Sub000Block161Part007
    + surrogateDiagTailX0RatChunk000Sub000Block161Part008
    + surrogateDiagTailX0RatChunk000Sub000Block161Part009
    + surrogateDiagTailX0RatChunk000Sub000Block161Part010
    + surrogateDiagTailX0RatChunk000Sub000Block161Part011
    + surrogateDiagTailX0RatChunk000Sub000Block161Part012
    + surrogateDiagTailX0RatChunk000Sub000Block161Part013
    + surrogateDiagTailX0RatChunk000Sub000Block161Part014
    + surrogateDiagTailX0RatChunk000Sub000Block161Part015
    + surrogateDiagTailX0RatChunk000Sub000Block161Part016
    + surrogateDiagTailX0RatChunk000Sub000Block161Part017
    + surrogateDiagTailX0RatChunk000Sub000Block161Part018
    + surrogateDiagTailX0RatChunk000Sub000Block161Part019
    + surrogateDiagTailX0RatChunk000Sub000Block161Part020
    + surrogateDiagTailX0RatChunk000Sub000Block161Part021
    + surrogateDiagTailX0RatChunk000Sub000Block161Part022
    + surrogateDiagTailX0RatChunk000Sub000Block161Part023
    + surrogateDiagTailX0RatChunk000Sub000Block161Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block161_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block161Head + surrogateDiagTailX0RatChunk000Sub000Block161Mid + surrogateDiagTailX0RatChunk000Sub000Block161Tail =
      surrogateDiagTailX0RatChunk000Sub000Block161 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block161Head surrogateDiagTailX0RatChunk000Sub000Block161Mid surrogateDiagTailX0RatChunk000Sub000Block161Tail surrogateDiagTailX0RatChunk000Sub000Block161
  ring

def SurrogateDiagonalTailChunk000Sub000Block161HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block161HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block161Head

def SurrogateDiagonalTailChunk000Sub000Block161MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block161MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block161Mid

def SurrogateDiagonalTailChunk000Sub000Block161TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block161TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block161Tail

theorem surrogateDiagonalTailChunk000Sub000Block161_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block161HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block161MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block161TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block161Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block161 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block161HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block161MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block161TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block161Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block161_eq_head_add_mid_add_tail

/-- Block 162 covers tail-support indices [4050,4075) and q from 6710 to 6751. -/

def TailChunk000Sub000Block162Part000SupportExplicit : Finset ℕ :=
  ([6710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part000 : ℚ :=
  (71869061 : ℚ) / 10370073600000

def SurrogateDiagonalTailChunk000Sub000Block162Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6710
    = surrogateDiagTailX0RatChunk000Sub000Block162Part000

theorem surrogateDiagonalTailChunk000Sub000Block162Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part000] using hcert

def TailChunk000Sub000Block162Part001SupportExplicit : Finset ℕ :=
  ([6711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part001 : ℚ :=
  (781639933175 : ℚ) / 500039189688689664

def SurrogateDiagonalTailChunk000Sub000Block162Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6711
    = surrogateDiagTailX0RatChunk000Sub000Block162Part001

theorem surrogateDiagonalTailChunk000Sub000Block162Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part001] using hcert

def TailChunk000Sub000Block162Part002SupportExplicit : Finset ℕ :=
  ([6715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part002 : ℚ :=
  (1960512982825 : ℚ) / 1552834479205122048

def SurrogateDiagonalTailChunk000Sub000Block162Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6715
    = surrogateDiagTailX0RatChunk000Sub000Block162Part002

theorem surrogateDiagonalTailChunk000Sub000Block162Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part002] using hcert

def TailChunk000Sub000Block162Part003SupportExplicit : Finset ℕ :=
  ([6717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part003 : ℚ :=
  (391519140925 : ℚ) / 250915320216797472

def SurrogateDiagonalTailChunk000Sub000Block162Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6717
    = surrogateDiagTailX0RatChunk000Sub000Block162Part003

theorem surrogateDiagonalTailChunk000Sub000Block162Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part003] using hcert

def TailChunk000Sub000Block162Part004SupportExplicit : Finset ℕ :=
  ([6718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part004 : ℚ :=
  (1410078052975 : ℚ) / 317943262324517448

def SurrogateDiagonalTailChunk000Sub000Block162Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6718
    = surrogateDiagTailX0RatChunk000Sub000Block162Part004

theorem surrogateDiagonalTailChunk000Sub000Block162Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part004] using hcert

def TailChunk000Sub000Block162Part005SupportExplicit : Finset ℕ :=
  ([6719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part005 : ℚ :=
  (705390015625 : ℚ) / 1273288643408930322

def SurrogateDiagonalTailChunk000Sub000Block162Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6719
    = surrogateDiagTailX0RatChunk000Sub000Block162Part005

theorem surrogateDiagonalTailChunk000Sub000Block162Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part005] using hcert

def TailChunk000Sub000Block162Part006SupportExplicit : Finset ℕ :=
  ([6721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part006 : ℚ :=
  (5846156977 : ℚ) / 6190873101434880

def SurrogateDiagonalTailChunk000Sub000Block162Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6721
    = surrogateDiagTailX0RatChunk000Sub000Block162Part006

theorem surrogateDiagonalTailChunk000Sub000Block162Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part006] using hcert

def TailChunk000Sub000Block162Part007SupportExplicit : Finset ℕ :=
  ([6722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part007 : ℚ :=
  (56470308679 : ℚ) / 12748055917363200

def SurrogateDiagonalTailChunk000Sub000Block162Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6722
    = surrogateDiagTailX0RatChunk000Sub000Block162Part007

theorem surrogateDiagonalTailChunk000Sub000Block162Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part007] using hcert

def TailChunk000Sub000Block162Part008SupportExplicit : Finset ℕ :=
  ([6726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part008 : ℚ :=
  (363205844525 : ℚ) / 23763961523856384

def SurrogateDiagonalTailChunk000Sub000Block162Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6726
    = surrogateDiagTailX0RatChunk000Sub000Block162Part008

theorem surrogateDiagonalTailChunk000Sub000Block162Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part008] using hcert

def TailChunk000Sub000Block162Part009SupportExplicit : Finset ℕ :=
  ([6729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part009 : ℚ :=
  (188558625 : ℚ) / 101065382584384

def SurrogateDiagonalTailChunk000Sub000Block162Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6729
    = surrogateDiagTailX0RatChunk000Sub000Block162Part009

theorem surrogateDiagonalTailChunk000Sub000Block162Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part009] using hcert

def TailChunk000Sub000Block162Part010SupportExplicit : Finset ℕ :=
  ([6730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part010 : ℚ :=
  (1073952865075 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block162Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6730
    = surrogateDiagTailX0RatChunk000Sub000Block162Part010

theorem surrogateDiagonalTailChunk000Sub000Block162Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part010] using hcert

def TailChunk000Sub000Block162Part011SupportExplicit : Finset ℕ :=
  ([6731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part011 : ℚ :=
  (1368724559375 : ℚ) / 2304052752306299904

def SurrogateDiagonalTailChunk000Sub000Block162Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6731
    = surrogateDiagTailX0RatChunk000Sub000Block162Part011

theorem surrogateDiagonalTailChunk000Sub000Block162Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part011] using hcert

def TailChunk000Sub000Block162Part012SupportExplicit : Finset ℕ :=
  ([6733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part012 : ℚ :=
  (708332640625 : ℚ) / 1283935765425283872

def SurrogateDiagonalTailChunk000Sub000Block162Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6733
    = surrogateDiagTailX0RatChunk000Sub000Block162Part012

theorem surrogateDiagonalTailChunk000Sub000Block162Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part012] using hcert

def TailChunk000Sub000Block162Part013SupportExplicit : Finset ℕ :=
  ([6734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part013 : ℚ :=
  (608200965775 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block162Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6734
    = surrogateDiagTailX0RatChunk000Sub000Block162Part013

theorem surrogateDiagonalTailChunk000Sub000Block162Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part013] using hcert

def TailChunk000Sub000Block162Part014SupportExplicit : Finset ℕ :=
  ([6735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part014 : ℚ :=
  (104943759225 : ℚ) / 68761859473276928

def SurrogateDiagonalTailChunk000Sub000Block162Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6735
    = surrogateDiagTailX0RatChunk000Sub000Block162Part014

theorem surrogateDiagonalTailChunk000Sub000Block162Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part014] using hcert

def TailChunk000Sub000Block162Part015SupportExplicit : Finset ℕ :=
  ([6737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block162Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6737
    = surrogateDiagTailX0RatChunk000Sub000Block162Part015

theorem surrogateDiagonalTailChunk000Sub000Block162Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part015] using hcert

def TailChunk000Sub000Block162Part016SupportExplicit : Finset ℕ :=
  ([6738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part016 : ℚ :=
  (551480950675 : ℚ) / 63404235329643648

def SurrogateDiagonalTailChunk000Sub000Block162Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6738
    = surrogateDiagTailX0RatChunk000Sub000Block162Part016

theorem surrogateDiagonalTailChunk000Sub000Block162Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part016] using hcert

def TailChunk000Sub000Block162Part017SupportExplicit : Finset ℕ :=
  ([6739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part017 : ℚ :=
  (32388597675 : ℚ) / 1419474951544477696

def SurrogateDiagonalTailChunk000Sub000Block162Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6739
    = surrogateDiagTailX0RatChunk000Sub000Block162Part017

theorem surrogateDiagonalTailChunk000Sub000Block162Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part017] using hcert

def TailChunk000Sub000Block162Part018SupportExplicit : Finset ℕ :=
  ([6742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part018 : ℚ :=
  (284091025 : ℚ) / 129004973445522

def SurrogateDiagonalTailChunk000Sub000Block162Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6742
    = surrogateDiagTailX0RatChunk000Sub000Block162Part018

theorem surrogateDiagonalTailChunk000Sub000Block162Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part018] using hcert

def TailChunk000Sub000Block162Part019SupportExplicit : Finset ℕ :=
  ([6743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part019 : ℚ :=
  (2535151321 : ℚ) / 46770421525862400

def SurrogateDiagonalTailChunk000Sub000Block162Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6743
    = surrogateDiagTailX0RatChunk000Sub000Block162Part019

theorem surrogateDiagonalTailChunk000Sub000Block162Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part019] using hcert

def TailChunk000Sub000Block162Part020SupportExplicit : Finset ℕ :=
  ([6745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part020 : ℚ :=
  (10067565227 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub000Block162Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6745
    = surrogateDiagTailX0RatChunk000Sub000Block162Part020

theorem surrogateDiagonalTailChunk000Sub000Block162Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part020] using hcert

def TailChunk000Sub000Block162Part021SupportExplicit : Finset ℕ :=
  ([6746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part021 : ℚ :=
  (177767640625 : ℚ) / 80819680896198432

def SurrogateDiagonalTailChunk000Sub000Block162Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6746
    = surrogateDiagTailX0RatChunk000Sub000Block162Part021

theorem surrogateDiagonalTailChunk000Sub000Block162Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part021] using hcert

def TailChunk000Sub000Block162Part022SupportExplicit : Finset ℕ :=
  ([6747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part022 : ℚ :=
  (322619682125 : ℚ) / 363040952256036864

def SurrogateDiagonalTailChunk000Sub000Block162Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6747
    = surrogateDiagTailX0RatChunk000Sub000Block162Part022

theorem surrogateDiagonalTailChunk000Sub000Block162Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part022] using hcert

def TailChunk000Sub000Block162Part023SupportExplicit : Finset ℕ :=
  ([6749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part023 : ℚ :=
  (132104295025 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk000Sub000Block162Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6749
    = surrogateDiagTailX0RatChunk000Sub000Block162Part023

theorem surrogateDiagonalTailChunk000Sub000Block162Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part023] using hcert

def TailChunk000Sub000Block162Part024SupportExplicit : Finset ℕ :=
  ([6751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part024 : ℚ :=
  (30783794225 : ℚ) / 2304052752306299904

def SurrogateDiagonalTailChunk000Sub000Block162Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6751
    = surrogateDiagTailX0RatChunk000Sub000Block162Part024

theorem surrogateDiagonalTailChunk000Sub000Block162Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block162HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block162Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block162Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block162Part000
    + surrogateDiagTailX0RatChunk000Sub000Block162Part001
    + surrogateDiagTailX0RatChunk000Sub000Block162Part002
    + surrogateDiagTailX0RatChunk000Sub000Block162Part003
    + surrogateDiagTailX0RatChunk000Sub000Block162Part004
    + surrogateDiagTailX0RatChunk000Sub000Block162Part005
    + surrogateDiagTailX0RatChunk000Sub000Block162Part006
    + surrogateDiagTailX0RatChunk000Sub000Block162Part007
    + surrogateDiagTailX0RatChunk000Sub000Block162Part008
    + surrogateDiagTailX0RatChunk000Sub000Block162Part009

def surrogateDiagonalTailChunk000Sub000Block162MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block162Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block162Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block162Part010
    + surrogateDiagTailX0RatChunk000Sub000Block162Part011
    + surrogateDiagTailX0RatChunk000Sub000Block162Part012
    + surrogateDiagTailX0RatChunk000Sub000Block162Part013
    + surrogateDiagTailX0RatChunk000Sub000Block162Part014
    + surrogateDiagTailX0RatChunk000Sub000Block162Part015
    + surrogateDiagTailX0RatChunk000Sub000Block162Part016
    + surrogateDiagTailX0RatChunk000Sub000Block162Part017
    + surrogateDiagTailX0RatChunk000Sub000Block162Part018
    + surrogateDiagTailX0RatChunk000Sub000Block162Part019

def surrogateDiagonalTailChunk000Sub000Block162TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block162Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block162Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block162Part020
    + surrogateDiagTailX0RatChunk000Sub000Block162Part021
    + surrogateDiagTailX0RatChunk000Sub000Block162Part022
    + surrogateDiagTailX0RatChunk000Sub000Block162Part023
    + surrogateDiagTailX0RatChunk000Sub000Block162Part024

def surrogateDiagonalTailChunk000Sub000Block162Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block162HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block162MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block162TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block162 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block162Part000
    + surrogateDiagTailX0RatChunk000Sub000Block162Part001
    + surrogateDiagTailX0RatChunk000Sub000Block162Part002
    + surrogateDiagTailX0RatChunk000Sub000Block162Part003
    + surrogateDiagTailX0RatChunk000Sub000Block162Part004
    + surrogateDiagTailX0RatChunk000Sub000Block162Part005
    + surrogateDiagTailX0RatChunk000Sub000Block162Part006
    + surrogateDiagTailX0RatChunk000Sub000Block162Part007
    + surrogateDiagTailX0RatChunk000Sub000Block162Part008
    + surrogateDiagTailX0RatChunk000Sub000Block162Part009
    + surrogateDiagTailX0RatChunk000Sub000Block162Part010
    + surrogateDiagTailX0RatChunk000Sub000Block162Part011
    + surrogateDiagTailX0RatChunk000Sub000Block162Part012
    + surrogateDiagTailX0RatChunk000Sub000Block162Part013
    + surrogateDiagTailX0RatChunk000Sub000Block162Part014
    + surrogateDiagTailX0RatChunk000Sub000Block162Part015
    + surrogateDiagTailX0RatChunk000Sub000Block162Part016
    + surrogateDiagTailX0RatChunk000Sub000Block162Part017
    + surrogateDiagTailX0RatChunk000Sub000Block162Part018
    + surrogateDiagTailX0RatChunk000Sub000Block162Part019
    + surrogateDiagTailX0RatChunk000Sub000Block162Part020
    + surrogateDiagTailX0RatChunk000Sub000Block162Part021
    + surrogateDiagTailX0RatChunk000Sub000Block162Part022
    + surrogateDiagTailX0RatChunk000Sub000Block162Part023
    + surrogateDiagTailX0RatChunk000Sub000Block162Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block162_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block162Head + surrogateDiagTailX0RatChunk000Sub000Block162Mid + surrogateDiagTailX0RatChunk000Sub000Block162Tail =
      surrogateDiagTailX0RatChunk000Sub000Block162 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block162Head surrogateDiagTailX0RatChunk000Sub000Block162Mid surrogateDiagTailX0RatChunk000Sub000Block162Tail surrogateDiagTailX0RatChunk000Sub000Block162
  ring

def SurrogateDiagonalTailChunk000Sub000Block162HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block162HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block162Head

def SurrogateDiagonalTailChunk000Sub000Block162MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block162MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block162Mid

def SurrogateDiagonalTailChunk000Sub000Block162TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block162TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block162Tail

theorem surrogateDiagonalTailChunk000Sub000Block162_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block162HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block162MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block162TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block162Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block162 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block162HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block162MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block162TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block162Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block162_eq_head_add_mid_add_tail

/-- Block 163 covers tail-support indices [4075,4100) and q from 6753 to 6791. -/

def TailChunk000Sub000Block163Part000SupportExplicit : Finset ℕ :=
  ([6753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part000 : ℚ :=
  (12666216749 : ℚ) / 20507225625000000

def SurrogateDiagonalTailChunk000Sub000Block163Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6753
    = surrogateDiagTailX0RatChunk000Sub000Block163Part000

theorem surrogateDiagonalTailChunk000Sub000Block163Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part000] using hcert

def TailChunk000Sub000Block163Part001SupportExplicit : Finset ℕ :=
  ([6754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part001 : ℚ :=
  (360658697 : ℚ) / 116926053814656

def SurrogateDiagonalTailChunk000Sub000Block163Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6754
    = surrogateDiagTailX0RatChunk000Sub000Block163Part001

theorem surrogateDiagonalTailChunk000Sub000Block163Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part001] using hcert

def TailChunk000Sub000Block163Part002SupportExplicit : Finset ℕ :=
  ([6755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part002 : ℚ :=
  (482026076125 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub000Block163Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6755
    = surrogateDiagTailX0RatChunk000Sub000Block163Part002

theorem surrogateDiagonalTailChunk000Sub000Block163Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part002] using hcert

def TailChunk000Sub000Block163Part003SupportExplicit : Finset ℕ :=
  ([6757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part003 : ℚ :=
  (226434087975 : ℚ) / 371047643509817344

def SurrogateDiagonalTailChunk000Sub000Block163Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6757
    = surrogateDiagTailX0RatChunk000Sub000Block163Part003

theorem surrogateDiagonalTailChunk000Sub000Block163Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part003] using hcert

def TailChunk000Sub000Block163Part004SupportExplicit : Finset ℕ :=
  ([6758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part004 : ℚ :=
  (27075034949 : ℚ) / 5511082284057600

def SurrogateDiagonalTailChunk000Sub000Block163Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6758
    = surrogateDiagTailX0RatChunk000Sub000Block163Part004

theorem surrogateDiagonalTailChunk000Sub000Block163Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part004] using hcert

def TailChunk000Sub000Block163Part005SupportExplicit : Finset ℕ :=
  ([6761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part005 : ℚ :=
  (1142778025 : ℚ) / 2088688299889152

def SurrogateDiagonalTailChunk000Sub000Block163Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6761
    = surrogateDiagTailX0RatChunk000Sub000Block163Part005

theorem surrogateDiagonalTailChunk000Sub000Block163Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part005] using hcert

def TailChunk000Sub000Block163Part006SupportExplicit : Finset ℕ :=
  ([6763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part006 : ℚ :=
  (714658890625 : ℚ) / 1306975760962825842

def SurrogateDiagonalTailChunk000Sub000Block163Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6763
    = surrogateDiagTailX0RatChunk000Sub000Block163Part006

theorem surrogateDiagonalTailChunk000Sub000Block163Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part006] using hcert

def TailChunk000Sub000Block163Part007SupportExplicit : Finset ℕ :=
  ([6765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part007 : ℚ :=
  (21816962357 : ℚ) / 5243928576000000

def SurrogateDiagonalTailChunk000Sub000Block163Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6765
    = surrogateDiagTailX0RatChunk000Sub000Block163Part007

theorem surrogateDiagonalTailChunk000Sub000Block163Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part007] using hcert

def TailChunk000Sub000Block163Part008SupportExplicit : Finset ℕ :=
  ([6766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part008 : ℚ :=
  (219345239875 : ℚ) / 41977473890254848

def SurrogateDiagonalTailChunk000Sub000Block163Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6766
    = surrogateDiagTailX0RatChunk000Sub000Block163Part008

theorem surrogateDiagonalTailChunk000Sub000Block163Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part008] using hcert

def TailChunk000Sub000Block163Part009SupportExplicit : Finset ℕ :=
  ([6767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part009 : ℚ :=
  (55481903993 : ℚ) / 94892654736000000

def SurrogateDiagonalTailChunk000Sub000Block163Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6767
    = surrogateDiagTailX0RatChunk000Sub000Block163Part009

theorem surrogateDiagonalTailChunk000Sub000Block163Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part009] using hcert

def TailChunk000Sub000Block163Part010SupportExplicit : Finset ℕ :=
  ([6769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part010 : ℚ :=
  (2335181990275 : ℚ) / 2821891855406617728

def SurrogateDiagonalTailChunk000Sub000Block163Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6769
    = surrogateDiagTailX0RatChunk000Sub000Block163Part010

theorem surrogateDiagonalTailChunk000Sub000Block163Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part010] using hcert

def TailChunk000Sub000Block163Part011SupportExplicit : Finset ℕ :=
  ([6770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part011 : ℚ :=
  (1058165929525 : ℚ) / 133676051192905728

def SurrogateDiagonalTailChunk000Sub000Block163Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6770
    = surrogateDiagTailX0RatChunk000Sub000Block163Part011

theorem surrogateDiagonalTailChunk000Sub000Block163Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part011] using hcert

def TailChunk000Sub000Block163Part012SupportExplicit : Finset ℕ :=
  ([6771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part012 : ℚ :=
  (12126794669 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk000Sub000Block163Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6771
    = surrogateDiagTailX0RatChunk000Sub000Block163Part012

theorem surrogateDiagonalTailChunk000Sub000Block163Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part012] using hcert

def TailChunk000Sub000Block163Part013SupportExplicit : Finset ℕ :=
  ([6773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part013 : ℚ :=
  (103597257811 : ℚ) / 151643992109875200

def SurrogateDiagonalTailChunk000Sub000Block163Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6773
    = surrogateDiagTailX0RatChunk000Sub000Block163Part013

theorem surrogateDiagonalTailChunk000Sub000Block163Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part013] using hcert

def TailChunk000Sub000Block163Part014SupportExplicit : Finset ℕ :=
  ([6774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part014 : ℚ :=
  (875547582175 : ℚ) / 64771393426587648

def SurrogateDiagonalTailChunk000Sub000Block163Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6774
    = surrogateDiagTailX0RatChunk000Sub000Block163Part014

theorem surrogateDiagonalTailChunk000Sub000Block163Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part014] using hcert

def TailChunk000Sub000Block163Part015SupportExplicit : Finset ℕ :=
  ([6778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part015 : ℚ :=
  (1435377991975 : ℚ) / 329458309386019968

def SurrogateDiagonalTailChunk000Sub000Block163Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6778
    = surrogateDiagTailX0RatChunk000Sub000Block163Part015

theorem surrogateDiagonalTailChunk000Sub000Block163Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part015] using hcert

def TailChunk000Sub000Block163Part016SupportExplicit : Finset ℕ :=
  ([6779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part016 : ℚ :=
  (718044390625 : ℚ) / 1319389809927356082

def SurrogateDiagonalTailChunk000Sub000Block163Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6779
    = surrogateDiagTailX0RatChunk000Sub000Block163Part016

theorem surrogateDiagonalTailChunk000Sub000Block163Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part016] using hcert

def TailChunk000Sub000Block163Part017SupportExplicit : Finset ℕ :=
  ([6781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part017 : ℚ :=
  (1149549025 : ℚ) / 2113516417319712

def SurrogateDiagonalTailChunk000Sub000Block163Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6781
    = surrogateDiagTailX0RatChunk000Sub000Block163Part017

theorem surrogateDiagonalTailChunk000Sub000Block163Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part017] using hcert

def TailChunk000Sub000Block163Part018SupportExplicit : Finset ℕ :=
  ([6782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part018 : ℚ :=
  (287472025 : ℚ) / 132094776082482

def SurrogateDiagonalTailChunk000Sub000Block163Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6782
    = surrogateDiagTailX0RatChunk000Sub000Block163Part018

theorem surrogateDiagonalTailChunk000Sub000Block163Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part018] using hcert

def TailChunk000Sub000Block163Part019SupportExplicit : Finset ℕ :=
  ([6783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part019 : ℚ :=
  (99857304275 : ℚ) / 29726278894485504

def SurrogateDiagonalTailChunk000Sub000Block163Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6783
    = surrogateDiagTailX0RatChunk000Sub000Block163Part019

theorem surrogateDiagonalTailChunk000Sub000Block163Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part019] using hcert

def TailChunk000Sub000Block163Part020SupportExplicit : Finset ℕ :=
  ([6785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part020 : ℚ :=
  (2028464625175 : ℚ) / 1696951858171772928

def SurrogateDiagonalTailChunk000Sub000Block163Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6785
    = surrogateDiagTailX0RatChunk000Sub000Block163Part020

theorem surrogateDiagonalTailChunk000Sub000Block163Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part020] using hcert

def TailChunk000Sub000Block163Part021SupportExplicit : Finset ℕ :=
  ([6787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part021 : ℚ :=
  (101647947661 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub000Block163Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6787
    = surrogateDiagTailX0RatChunk000Sub000Block163Part021

theorem surrogateDiagonalTailChunk000Sub000Block163Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part021] using hcert

def TailChunk000Sub000Block163Part022SupportExplicit : Finset ℕ :=
  ([6789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part022 : ℚ :=
  (72394476889 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block163Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6789
    = surrogateDiagTailX0RatChunk000Sub000Block163Part022

theorem surrogateDiagonalTailChunk000Sub000Block163Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part022] using hcert

def TailChunk000Sub000Block163Part023SupportExplicit : Finset ℕ :=
  ([6790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part023 : ℚ :=
  (576036452275 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block163Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6790
    = surrogateDiagTailX0RatChunk000Sub000Block163Part023

theorem surrogateDiagonalTailChunk000Sub000Block163Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part023] using hcert

def TailChunk000Sub000Block163Part024SupportExplicit : Finset ℕ :=
  ([6791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part024 : ℚ :=
  (1152942025 : ℚ) / 2126013154417362

def SurrogateDiagonalTailChunk000Sub000Block163Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6791
    = surrogateDiagTailX0RatChunk000Sub000Block163Part024

theorem surrogateDiagonalTailChunk000Sub000Block163Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block163HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block163Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block163Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block163Part000
    + surrogateDiagTailX0RatChunk000Sub000Block163Part001
    + surrogateDiagTailX0RatChunk000Sub000Block163Part002
    + surrogateDiagTailX0RatChunk000Sub000Block163Part003
    + surrogateDiagTailX0RatChunk000Sub000Block163Part004
    + surrogateDiagTailX0RatChunk000Sub000Block163Part005
    + surrogateDiagTailX0RatChunk000Sub000Block163Part006
    + surrogateDiagTailX0RatChunk000Sub000Block163Part007
    + surrogateDiagTailX0RatChunk000Sub000Block163Part008
    + surrogateDiagTailX0RatChunk000Sub000Block163Part009

def surrogateDiagonalTailChunk000Sub000Block163MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block163Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block163Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block163Part010
    + surrogateDiagTailX0RatChunk000Sub000Block163Part011
    + surrogateDiagTailX0RatChunk000Sub000Block163Part012
    + surrogateDiagTailX0RatChunk000Sub000Block163Part013
    + surrogateDiagTailX0RatChunk000Sub000Block163Part014
    + surrogateDiagTailX0RatChunk000Sub000Block163Part015
    + surrogateDiagTailX0RatChunk000Sub000Block163Part016
    + surrogateDiagTailX0RatChunk000Sub000Block163Part017
    + surrogateDiagTailX0RatChunk000Sub000Block163Part018
    + surrogateDiagTailX0RatChunk000Sub000Block163Part019

def surrogateDiagonalTailChunk000Sub000Block163TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block163Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block163Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block163Part020
    + surrogateDiagTailX0RatChunk000Sub000Block163Part021
    + surrogateDiagTailX0RatChunk000Sub000Block163Part022
    + surrogateDiagTailX0RatChunk000Sub000Block163Part023
    + surrogateDiagTailX0RatChunk000Sub000Block163Part024

def surrogateDiagonalTailChunk000Sub000Block163Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block163HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block163MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block163TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block163 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block163Part000
    + surrogateDiagTailX0RatChunk000Sub000Block163Part001
    + surrogateDiagTailX0RatChunk000Sub000Block163Part002
    + surrogateDiagTailX0RatChunk000Sub000Block163Part003
    + surrogateDiagTailX0RatChunk000Sub000Block163Part004
    + surrogateDiagTailX0RatChunk000Sub000Block163Part005
    + surrogateDiagTailX0RatChunk000Sub000Block163Part006
    + surrogateDiagTailX0RatChunk000Sub000Block163Part007
    + surrogateDiagTailX0RatChunk000Sub000Block163Part008
    + surrogateDiagTailX0RatChunk000Sub000Block163Part009
    + surrogateDiagTailX0RatChunk000Sub000Block163Part010
    + surrogateDiagTailX0RatChunk000Sub000Block163Part011
    + surrogateDiagTailX0RatChunk000Sub000Block163Part012
    + surrogateDiagTailX0RatChunk000Sub000Block163Part013
    + surrogateDiagTailX0RatChunk000Sub000Block163Part014
    + surrogateDiagTailX0RatChunk000Sub000Block163Part015
    + surrogateDiagTailX0RatChunk000Sub000Block163Part016
    + surrogateDiagTailX0RatChunk000Sub000Block163Part017
    + surrogateDiagTailX0RatChunk000Sub000Block163Part018
    + surrogateDiagTailX0RatChunk000Sub000Block163Part019
    + surrogateDiagTailX0RatChunk000Sub000Block163Part020
    + surrogateDiagTailX0RatChunk000Sub000Block163Part021
    + surrogateDiagTailX0RatChunk000Sub000Block163Part022
    + surrogateDiagTailX0RatChunk000Sub000Block163Part023
    + surrogateDiagTailX0RatChunk000Sub000Block163Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block163_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block163Head + surrogateDiagTailX0RatChunk000Sub000Block163Mid + surrogateDiagTailX0RatChunk000Sub000Block163Tail =
      surrogateDiagTailX0RatChunk000Sub000Block163 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block163Head surrogateDiagTailX0RatChunk000Sub000Block163Mid surrogateDiagTailX0RatChunk000Sub000Block163Tail surrogateDiagTailX0RatChunk000Sub000Block163
  ring

def SurrogateDiagonalTailChunk000Sub000Block163HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block163HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block163Head

def SurrogateDiagonalTailChunk000Sub000Block163MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block163MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block163Mid

def SurrogateDiagonalTailChunk000Sub000Block163TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block163TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block163Tail

theorem surrogateDiagonalTailChunk000Sub000Block163_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block163HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block163MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block163TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block163Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block163 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block163HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block163MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block163TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block163Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block163_eq_head_add_mid_add_tail

/-- Block 164 covers tail-support indices [4100,4125) and q from 6793 to 6833. -/

def TailChunk000Sub000Block164Part000SupportExplicit : Finset ℕ :=
  ([6793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part000 : ℚ :=
  (721013265625 : ℚ) / 1330324460588339712

def SurrogateDiagonalTailChunk000Sub000Block164Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6793
    = surrogateDiagTailX0RatChunk000Sub000Block164Part000

theorem surrogateDiagonalTailChunk000Sub000Block164Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part000] using hcert

def TailChunk000Sub000Block164Part001SupportExplicit : Finset ℕ :=
  ([6794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part001 : ℚ :=
  (707535959125 : ℚ) / 288006594038287488

def SurrogateDiagonalTailChunk000Sub000Block164Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6794
    = surrogateDiagTailX0RatChunk000Sub000Block164Part001

theorem surrogateDiagonalTailChunk000Sub000Block164Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part001] using hcert

def TailChunk000Sub000Block164Part002SupportExplicit : Finset ℕ :=
  ([6797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part002 : ℚ :=
  (96535954087 : ℚ) / 114756894965635200

def SurrogateDiagonalTailChunk000Sub000Block164Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6797
    = surrogateDiagTailX0RatChunk000Sub000Block164Part002

theorem surrogateDiagonalTailChunk000Sub000Block164Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part002] using hcert

def TailChunk000Sub000Block164Part003SupportExplicit : Finset ℕ :=
  ([6798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part003 : ℚ :=
  (20773894711 : ℚ) / 1732237834291200

def SurrogateDiagonalTailChunk000Sub000Block164Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6798
    = surrogateDiagTailX0RatChunk000Sub000Block164Part003

theorem surrogateDiagonalTailChunk000Sub000Block164Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part003] using hcert

def TailChunk000Sub000Block164Part004SupportExplicit : Finset ℕ :=
  ([6799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part004 : ℚ :=
  (6001865675 : ℚ) / 8911485571446144

def SurrogateDiagonalTailChunk000Sub000Block164Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6799
    = surrogateDiagTailX0RatChunk000Sub000Block164Part004

theorem surrogateDiagonalTailChunk000Sub000Block164Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part004] using hcert

def TailChunk000Sub000Block164Part005SupportExplicit : Finset ℕ :=
  ([6801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part005 : ℚ :=
  (200686608575 : ℚ) / 131854961616859536

def SurrogateDiagonalTailChunk000Sub000Block164Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6801
    = surrogateDiagTailX0RatChunk000Sub000Block164Part005

theorem surrogateDiagonalTailChunk000Sub000Block164Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part005] using hcert

def TailChunk000Sub000Block164Part006SupportExplicit : Finset ℕ :=
  ([6802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part006 : ℚ :=
  (700775540425 : ℚ) / 263509871084569728

def SurrogateDiagonalTailChunk000Sub000Block164Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6802
    = surrogateDiagTailX0RatChunk000Sub000Block164Part006

theorem surrogateDiagonalTailChunk000Sub000Block164Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part006] using hcert

def TailChunk000Sub000Block164Part007SupportExplicit : Finset ℕ :=
  ([6803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part007 : ℚ :=
  (723137640625 : ℚ) / 1338176435506757202

def SurrogateDiagonalTailChunk000Sub000Block164Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6803
    = surrogateDiagTailX0RatChunk000Sub000Block164Part007

theorem surrogateDiagonalTailChunk000Sub000Block164Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part007] using hcert

def TailChunk000Sub000Block164Part008SupportExplicit : Finset ℕ :=
  ([6805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part008 : ℚ :=
  (43961326487 : ℚ) / 43797815859609600

def SurrogateDiagonalTailChunk000Sub000Block164Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6805
    = surrogateDiagTailX0RatChunk000Sub000Block164Part008

theorem surrogateDiagonalTailChunk000Sub000Block164Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part008] using hcert

def TailChunk000Sub000Block164Part009SupportExplicit : Finset ℕ :=
  ([6806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part009 : ℚ :=
  (27634209497 : ℚ) / 5788315959705600

def SurrogateDiagonalTailChunk000Sub000Block164Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6806
    = surrogateDiagTailX0RatChunk000Sub000Block164Part009

theorem surrogateDiagonalTailChunk000Sub000Block164Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part009] using hcert

def TailChunk000Sub000Block164Part010SupportExplicit : Finset ℕ :=
  ([6807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part010 : ℚ :=
  (804163535975 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk000Sub000Block164Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6807
    = surrogateDiagTailX0RatChunk000Sub000Block164Part010

theorem surrogateDiagonalTailChunk000Sub000Block164Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part010] using hcert

def TailChunk000Sub000Block164Part011SupportExplicit : Finset ℕ :=
  ([6809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part011 : ℚ :=
  (102308258599 : ℚ) / 145895114964355200

def SurrogateDiagonalTailChunk000Sub000Block164Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6809
    = surrogateDiagTailX0RatChunk000Sub000Block164Part011

theorem surrogateDiagonalTailChunk000Sub000Block164Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part011] using hcert

def TailChunk000Sub000Block164Part012SupportExplicit : Finset ℕ :=
  ([6810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part012 : ℚ :=
  (309318733925 : ℚ) / 13359511181082624

def SurrogateDiagonalTailChunk000Sub000Block164Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6810
    = surrogateDiagTailX0RatChunk000Sub000Block164Part012

theorem surrogateDiagonalTailChunk000Sub000Block164Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part012] using hcert

def TailChunk000Sub000Block164Part013SupportExplicit : Finset ℕ :=
  ([6814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part013 : ℚ :=
  (1450665933775 : ℚ) / 336515779445189448

def SurrogateDiagonalTailChunk000Sub000Block164Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6814
    = surrogateDiagTailX0RatChunk000Sub000Block164Part013

theorem surrogateDiagonalTailChunk000Sub000Block164Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part013] using hcert

def TailChunk000Sub000Block164Part014SupportExplicit : Finset ℕ :=
  ([6815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part014 : ℚ :=
  (1028607515675 : ℚ) / 880846596536008704

def SurrogateDiagonalTailChunk000Sub000Block164Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6815
    = surrogateDiagTailX0RatChunk000Sub000Block164Part014

theorem surrogateDiagonalTailChunk000Sub000Block164Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part014] using hcert

def TailChunk000Sub000Block164Part015SupportExplicit : Finset ℕ :=
  ([6817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part015 : ℚ :=
  (107419446127 : ℚ) / 167805714432000000

def SurrogateDiagonalTailChunk000Sub000Block164Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6817
    = surrogateDiagTailX0RatChunk000Sub000Block164Part015

theorem surrogateDiagonalTailChunk000Sub000Block164Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part015] using hcert

def TailChunk000Sub000Block164Part016SupportExplicit : Finset ℕ :=
  ([6818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part016 : ℚ :=
  (1183038427375 : ℚ) / 180791054328509568

def SurrogateDiagonalTailChunk000Sub000Block164Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6818
    = surrogateDiagTailX0RatChunk000Sub000Block164Part016

theorem surrogateDiagonalTailChunk000Sub000Block164Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part016] using hcert

def TailChunk000Sub000Block164Part017SupportExplicit : Finset ℕ :=
  ([6819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part017 : ℚ :=
  (193636875 : ℚ) / 106584315265024

def SurrogateDiagonalTailChunk000Sub000Block164Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6819
    = surrogateDiagTailX0RatChunk000Sub000Block164Part017

theorem surrogateDiagonalTailChunk000Sub000Block164Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part017] using hcert

def TailChunk000Sub000Block164Part018SupportExplicit : Finset ℕ :=
  ([6821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part018 : ℚ :=
  (676388904625 : ℚ) / 1077926117001537312

def SurrogateDiagonalTailChunk000Sub000Block164Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6821
    = surrogateDiagTailX0RatChunk000Sub000Block164Part018

theorem surrogateDiagonalTailChunk000Sub000Block164Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part018] using hcert

def TailChunk000Sub000Block164Part019SupportExplicit : Finset ℕ :=
  ([6823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part019 : ℚ :=
  (727395765625 : ℚ) / 1353984609535762482

def SurrogateDiagonalTailChunk000Sub000Block164Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6823
    = surrogateDiagTailX0RatChunk000Sub000Block164Part019

theorem surrogateDiagonalTailChunk000Sub000Block164Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part019] using hcert

def TailChunk000Sub000Block164Part020SupportExplicit : Finset ℕ :=
  ([6826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part020 : ℚ :=
  (182008890625 : ℚ) / 84723318376380192

def SurrogateDiagonalTailChunk000Sub000Block164Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6826
    = surrogateDiagTailX0RatChunk000Sub000Block164Part020

theorem surrogateDiagonalTailChunk000Sub000Block164Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part020] using hcert

def TailChunk000Sub000Block164Part021SupportExplicit : Finset ℕ :=
  ([6827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block164Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6827
    = surrogateDiagTailX0RatChunk000Sub000Block164Part021

theorem surrogateDiagonalTailChunk000Sub000Block164Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part021] using hcert

def TailChunk000Sub000Block164Part022SupportExplicit : Finset ℕ :=
  ([6829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block164Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6829
    = surrogateDiagTailX0RatChunk000Sub000Block164Part022

theorem surrogateDiagonalTailChunk000Sub000Block164Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part022] using hcert

def TailChunk000Sub000Block164Part023SupportExplicit : Finset ℕ :=
  ([6830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part023 : ℚ :=
  (640899822775 : ℚ) / 138485506203568128

def SurrogateDiagonalTailChunk000Sub000Block164Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6830
    = surrogateDiagTailX0RatChunk000Sub000Block164Part023

theorem surrogateDiagonalTailChunk000Sub000Block164Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part023] using hcert

def TailChunk000Sub000Block164Part024SupportExplicit : Finset ℕ :=
  ([6833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block164Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6833
    = surrogateDiagTailX0RatChunk000Sub000Block164Part024

theorem surrogateDiagonalTailChunk000Sub000Block164Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block164HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block164Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block164Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block164Part000
    + surrogateDiagTailX0RatChunk000Sub000Block164Part001
    + surrogateDiagTailX0RatChunk000Sub000Block164Part002
    + surrogateDiagTailX0RatChunk000Sub000Block164Part003
    + surrogateDiagTailX0RatChunk000Sub000Block164Part004
    + surrogateDiagTailX0RatChunk000Sub000Block164Part005
    + surrogateDiagTailX0RatChunk000Sub000Block164Part006
    + surrogateDiagTailX0RatChunk000Sub000Block164Part007
    + surrogateDiagTailX0RatChunk000Sub000Block164Part008
    + surrogateDiagTailX0RatChunk000Sub000Block164Part009

def surrogateDiagonalTailChunk000Sub000Block164MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block164Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block164Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block164Part010
    + surrogateDiagTailX0RatChunk000Sub000Block164Part011
    + surrogateDiagTailX0RatChunk000Sub000Block164Part012
    + surrogateDiagTailX0RatChunk000Sub000Block164Part013
    + surrogateDiagTailX0RatChunk000Sub000Block164Part014
    + surrogateDiagTailX0RatChunk000Sub000Block164Part015
    + surrogateDiagTailX0RatChunk000Sub000Block164Part016
    + surrogateDiagTailX0RatChunk000Sub000Block164Part017
    + surrogateDiagTailX0RatChunk000Sub000Block164Part018
    + surrogateDiagTailX0RatChunk000Sub000Block164Part019

def surrogateDiagonalTailChunk000Sub000Block164TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block164Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block164Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block164Part020
    + surrogateDiagTailX0RatChunk000Sub000Block164Part021
    + surrogateDiagTailX0RatChunk000Sub000Block164Part022
    + surrogateDiagTailX0RatChunk000Sub000Block164Part023
    + surrogateDiagTailX0RatChunk000Sub000Block164Part024

def surrogateDiagonalTailChunk000Sub000Block164Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block164HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block164MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block164TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block164 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block164Part000
    + surrogateDiagTailX0RatChunk000Sub000Block164Part001
    + surrogateDiagTailX0RatChunk000Sub000Block164Part002
    + surrogateDiagTailX0RatChunk000Sub000Block164Part003
    + surrogateDiagTailX0RatChunk000Sub000Block164Part004
    + surrogateDiagTailX0RatChunk000Sub000Block164Part005
    + surrogateDiagTailX0RatChunk000Sub000Block164Part006
    + surrogateDiagTailX0RatChunk000Sub000Block164Part007
    + surrogateDiagTailX0RatChunk000Sub000Block164Part008
    + surrogateDiagTailX0RatChunk000Sub000Block164Part009
    + surrogateDiagTailX0RatChunk000Sub000Block164Part010
    + surrogateDiagTailX0RatChunk000Sub000Block164Part011
    + surrogateDiagTailX0RatChunk000Sub000Block164Part012
    + surrogateDiagTailX0RatChunk000Sub000Block164Part013
    + surrogateDiagTailX0RatChunk000Sub000Block164Part014
    + surrogateDiagTailX0RatChunk000Sub000Block164Part015
    + surrogateDiagTailX0RatChunk000Sub000Block164Part016
    + surrogateDiagTailX0RatChunk000Sub000Block164Part017
    + surrogateDiagTailX0RatChunk000Sub000Block164Part018
    + surrogateDiagTailX0RatChunk000Sub000Block164Part019
    + surrogateDiagTailX0RatChunk000Sub000Block164Part020
    + surrogateDiagTailX0RatChunk000Sub000Block164Part021
    + surrogateDiagTailX0RatChunk000Sub000Block164Part022
    + surrogateDiagTailX0RatChunk000Sub000Block164Part023
    + surrogateDiagTailX0RatChunk000Sub000Block164Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block164_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block164Head + surrogateDiagTailX0RatChunk000Sub000Block164Mid + surrogateDiagTailX0RatChunk000Sub000Block164Tail =
      surrogateDiagTailX0RatChunk000Sub000Block164 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block164Head surrogateDiagTailX0RatChunk000Sub000Block164Mid surrogateDiagTailX0RatChunk000Sub000Block164Tail surrogateDiagTailX0RatChunk000Sub000Block164
  ring

def SurrogateDiagonalTailChunk000Sub000Block164HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block164HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block164Head

def SurrogateDiagonalTailChunk000Sub000Block164MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block164MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block164Mid

def SurrogateDiagonalTailChunk000Sub000Block164TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block164TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block164Tail

theorem surrogateDiagonalTailChunk000Sub000Block164_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block164HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block164MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block164TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block164Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block164 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block164HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block164MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block164TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block164Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block164_eq_head_add_mid_add_tail

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

/-- Block 166 covers tail-support indices [4150,4175) and q from 6878 to 6918. -/

def TailChunk000Sub000Block166Part000SupportExplicit : Finset ℕ :=
  ([6878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part000 : ℚ :=
  (28659408187 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub000Block166Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6878
    = surrogateDiagTailX0RatChunk000Sub000Block166Part000

theorem surrogateDiagonalTailChunk000Sub000Block166Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part000] using hcert

def TailChunk000Sub000Block166Part001SupportExplicit : Finset ℕ :=
  ([6879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part001 : ℚ :=
  (821266271675 : ℚ) / 552046040204534784

def SurrogateDiagonalTailChunk000Sub000Block166Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6879
    = surrogateDiagTailX0RatChunk000Sub000Block166Part001

theorem surrogateDiagonalTailChunk000Sub000Block166Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part001] using hcert

def TailChunk000Sub000Block166Part002SupportExplicit : Finset ℕ :=
  ([6881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part002 : ℚ :=
  (2413116011875 : ℚ) / 3013545906065720448

def SurrogateDiagonalTailChunk000Sub000Block166Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6881
    = surrogateDiagTailX0RatChunk000Sub000Block166Part002

theorem surrogateDiagonalTailChunk000Sub000Block166Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part002] using hcert

def TailChunk000Sub000Block166Part003SupportExplicit : Finset ℕ :=
  ([6882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part003 : ℚ :=
  (1383969529 : ℚ) / 120956538470400

def SurrogateDiagonalTailChunk000Sub000Block166Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6882
    = surrogateDiagTailX0RatChunk000Sub000Block166Part003

theorem surrogateDiagonalTailChunk000Sub000Block166Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part003] using hcert

def TailChunk000Sub000Block166Part004SupportExplicit : Finset ℕ :=
  ([6883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part004 : ℚ :=
  (740245140625 : ℚ) / 1402250297094232722

def SurrogateDiagonalTailChunk000Sub000Block166Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6883
    = surrogateDiagTailX0RatChunk000Sub000Block166Part004

theorem surrogateDiagonalTailChunk000Sub000Block166Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part004] using hcert

def TailChunk000Sub000Block166Part005SupportExplicit : Finset ℕ :=
  ([6886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part005 : ℚ :=
  (1874374591 : ℚ) / 631849967124480

def SurrogateDiagonalTailChunk000Sub000Block166Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6886
    = surrogateDiagTailX0RatChunk000Sub000Block166Part005

theorem surrogateDiagonalTailChunk000Sub000Block166Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part005] using hcert

def TailChunk000Sub000Block166Part006SupportExplicit : Finset ℕ :=
  ([6887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part006 : ℚ :=
  (1436871497 : ℚ) / 2549611183472640

def SurrogateDiagonalTailChunk000Sub000Block166Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6887
    = surrogateDiagTailX0RatChunk000Sub000Block166Part006

theorem surrogateDiagonalTailChunk000Sub000Block166Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part006] using hcert

def TailChunk000Sub000Block166Part007SupportExplicit : Finset ℕ :=
  ([6890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part007 : ℚ :=
  (203595638075 : ℚ) / 32350718316773376

def SurrogateDiagonalTailChunk000Sub000Block166Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6890
    = surrogateDiagTailX0RatChunk000Sub000Block166Part007

theorem surrogateDiagonalTailChunk000Sub000Block166Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part007] using hcert

def TailChunk000Sub000Block166Part008SupportExplicit : Finset ℕ :=
  ([6891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part008 : ℚ :=
  (824134230425 : ℚ) / 555909864770125824

def SurrogateDiagonalTailChunk000Sub000Block166Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6891
    = surrogateDiagTailX0RatChunk000Sub000Block166Part008

theorem surrogateDiagonalTailChunk000Sub000Block166Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part008] using hcert

def TailChunk000Sub000Block166Part009SupportExplicit : Finset ℕ :=
  ([6893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part009 : ℚ :=
  (115038398281 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub000Block166Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6893
    = surrogateDiagTailX0RatChunk000Sub000Block166Part009

theorem surrogateDiagonalTailChunk000Sub000Block166Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part009] using hcert

def TailChunk000Sub000Block166Part010SupportExplicit : Finset ℕ :=
  ([6895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part010 : ℚ :=
  (922283713625 : ℚ) / 612161645151780864

def SurrogateDiagonalTailChunk000Sub000Block166Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6895
    = surrogateDiagTailX0RatChunk000Sub000Block166Part010

theorem surrogateDiagonalTailChunk000Sub000Block166Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part010] using hcert

def TailChunk000Sub000Block166Part011SupportExplicit : Finset ℕ :=
  ([6898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part011 : ℚ :=
  (1486652734975 : ℚ) / 353423877640439808

def SurrogateDiagonalTailChunk000Sub000Block166Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6898
    = surrogateDiagTailX0RatChunk000Sub000Block166Part011

theorem surrogateDiagonalTailChunk000Sub000Block166Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part011] using hcert

def TailChunk000Sub000Block166Part012SupportExplicit : Finset ℕ :=
  ([6899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part012 : ℚ :=
  (743690640625 : ℚ) / 1415336242158312402

def SurrogateDiagonalTailChunk000Sub000Block166Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6899
    = surrogateDiagTailX0RatChunk000Sub000Block166Part012

theorem surrogateDiagonalTailChunk000Sub000Block166Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part012] using hcert

def TailChunk000Sub000Block166Part013SupportExplicit : Finset ℕ :=
  ([6901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part013 : ℚ :=
  (2884032181825 : ℚ) / 5135743061701135488

def SurrogateDiagonalTailChunk000Sub000Block166Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6901
    = surrogateDiagTailX0RatChunk000Sub000Block166Part013

theorem surrogateDiagonalTailChunk000Sub000Block166Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part013] using hcert

def TailChunk000Sub000Block166Part014SupportExplicit : Finset ℕ :=
  ([6902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part014 : ℚ :=
  (119777684975 : ℚ) / 14504454732644352

def SurrogateDiagonalTailChunk000Sub000Block166Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6902
    = surrogateDiagTailX0RatChunk000Sub000Block166Part014

theorem surrogateDiagonalTailChunk000Sub000Block166Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part014] using hcert

def TailChunk000Sub000Block166Part015SupportExplicit : Finset ℕ :=
  ([6905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part015 : ℚ :=
  (85761341317 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk000Sub000Block166Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6905
    = surrogateDiagTailX0RatChunk000Sub000Block166Part015

theorem surrogateDiagonalTailChunk000Sub000Block166Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part015] using hcert

def TailChunk000Sub000Block166Part016SupportExplicit : Finset ℕ :=
  ([6906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part016 : ℚ :=
  (16545723947 : ℚ) / 1399484841000000

def SurrogateDiagonalTailChunk000Sub000Block166Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6906
    = surrogateDiagTailX0RatChunk000Sub000Block166Part016

theorem surrogateDiagonalTailChunk000Sub000Block166Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part016] using hcert

def TailChunk000Sub000Block166Part017SupportExplicit : Finset ℕ :=
  ([6907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part017 : ℚ :=
  (745416390625 : ℚ) / 1421913454402525362

def SurrogateDiagonalTailChunk000Sub000Block166Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6907
    = surrogateDiagTailX0RatChunk000Sub000Block166Part017

theorem surrogateDiagonalTailChunk000Sub000Block166Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part017] using hcert

def TailChunk000Sub000Block166Part018SupportExplicit : Finset ℕ :=
  ([6910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part018 : ℚ :=
  (44095874959 : ℚ) / 5803943532595200

def SurrogateDiagonalTailChunk000Sub000Block166Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6910
    = surrogateDiagTailX0RatChunk000Sub000Block166Part018

theorem surrogateDiagonalTailChunk000Sub000Block166Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part018] using hcert

def TailChunk000Sub000Block166Part019SupportExplicit : Finset ℕ :=
  ([6911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part019 : ℚ :=
  (1194048025 : ℚ) / 2280337029820722

def SurrogateDiagonalTailChunk000Sub000Block166Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6911
    = surrogateDiagTailX0RatChunk000Sub000Block166Part019

theorem surrogateDiagonalTailChunk000Sub000Block166Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part019] using hcert

def TailChunk000Sub000Block166Part020SupportExplicit : Finset ℕ :=
  ([6913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part020 : ℚ :=
  (113869193047 : ℚ) / 196781273521027200

def SurrogateDiagonalTailChunk000Sub000Block166Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6913
    = surrogateDiagTailX0RatChunk000Sub000Block166Part020

theorem surrogateDiagonalTailChunk000Sub000Block166Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part020] using hcert

def TailChunk000Sub000Block166Part021SupportExplicit : Finset ℕ :=
  ([6914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part021 : ℚ :=
  (1493557353775 : ℚ) / 356715346733826048

def SurrogateDiagonalTailChunk000Sub000Block166Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6914
    = surrogateDiagTailX0RatChunk000Sub000Block166Part021

theorem surrogateDiagonalTailChunk000Sub000Block166Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part021] using hcert

def TailChunk000Sub000Block166Part022SupportExplicit : Finset ℕ :=
  ([6915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part022 : ℚ :=
  (3743037259 : ℚ) / 1146457981747200

def SurrogateDiagonalTailChunk000Sub000Block166Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6915
    = surrogateDiagTailX0RatChunk000Sub000Block166Part022

theorem surrogateDiagonalTailChunk000Sub000Block166Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part022] using hcert

def TailChunk000Sub000Block166Part023SupportExplicit : Finset ℕ :=
  ([6917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part023 : ℚ :=
  (747576390625 : ℚ) / 1430167175036719392

def SurrogateDiagonalTailChunk000Sub000Block166Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6917
    = surrogateDiagTailX0RatChunk000Sub000Block166Part023

theorem surrogateDiagonalTailChunk000Sub000Block166Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part023] using hcert

def TailChunk000Sub000Block166Part024SupportExplicit : Finset ℕ :=
  ([6918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part024 : ℚ :=
  (581332316425 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block166Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6918
    = surrogateDiagTailX0RatChunk000Sub000Block166Part024

theorem surrogateDiagonalTailChunk000Sub000Block166Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block166HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block166Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block166Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block166Part000
    + surrogateDiagTailX0RatChunk000Sub000Block166Part001
    + surrogateDiagTailX0RatChunk000Sub000Block166Part002
    + surrogateDiagTailX0RatChunk000Sub000Block166Part003
    + surrogateDiagTailX0RatChunk000Sub000Block166Part004
    + surrogateDiagTailX0RatChunk000Sub000Block166Part005
    + surrogateDiagTailX0RatChunk000Sub000Block166Part006
    + surrogateDiagTailX0RatChunk000Sub000Block166Part007
    + surrogateDiagTailX0RatChunk000Sub000Block166Part008
    + surrogateDiagTailX0RatChunk000Sub000Block166Part009

def surrogateDiagonalTailChunk000Sub000Block166MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block166Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block166Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block166Part010
    + surrogateDiagTailX0RatChunk000Sub000Block166Part011
    + surrogateDiagTailX0RatChunk000Sub000Block166Part012
    + surrogateDiagTailX0RatChunk000Sub000Block166Part013
    + surrogateDiagTailX0RatChunk000Sub000Block166Part014
    + surrogateDiagTailX0RatChunk000Sub000Block166Part015
    + surrogateDiagTailX0RatChunk000Sub000Block166Part016
    + surrogateDiagTailX0RatChunk000Sub000Block166Part017
    + surrogateDiagTailX0RatChunk000Sub000Block166Part018
    + surrogateDiagTailX0RatChunk000Sub000Block166Part019

def surrogateDiagonalTailChunk000Sub000Block166TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block166Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block166Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block166Part020
    + surrogateDiagTailX0RatChunk000Sub000Block166Part021
    + surrogateDiagTailX0RatChunk000Sub000Block166Part022
    + surrogateDiagTailX0RatChunk000Sub000Block166Part023
    + surrogateDiagTailX0RatChunk000Sub000Block166Part024

def surrogateDiagonalTailChunk000Sub000Block166Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block166HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block166MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block166TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block166 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block166Part000
    + surrogateDiagTailX0RatChunk000Sub000Block166Part001
    + surrogateDiagTailX0RatChunk000Sub000Block166Part002
    + surrogateDiagTailX0RatChunk000Sub000Block166Part003
    + surrogateDiagTailX0RatChunk000Sub000Block166Part004
    + surrogateDiagTailX0RatChunk000Sub000Block166Part005
    + surrogateDiagTailX0RatChunk000Sub000Block166Part006
    + surrogateDiagTailX0RatChunk000Sub000Block166Part007
    + surrogateDiagTailX0RatChunk000Sub000Block166Part008
    + surrogateDiagTailX0RatChunk000Sub000Block166Part009
    + surrogateDiagTailX0RatChunk000Sub000Block166Part010
    + surrogateDiagTailX0RatChunk000Sub000Block166Part011
    + surrogateDiagTailX0RatChunk000Sub000Block166Part012
    + surrogateDiagTailX0RatChunk000Sub000Block166Part013
    + surrogateDiagTailX0RatChunk000Sub000Block166Part014
    + surrogateDiagTailX0RatChunk000Sub000Block166Part015
    + surrogateDiagTailX0RatChunk000Sub000Block166Part016
    + surrogateDiagTailX0RatChunk000Sub000Block166Part017
    + surrogateDiagTailX0RatChunk000Sub000Block166Part018
    + surrogateDiagTailX0RatChunk000Sub000Block166Part019
    + surrogateDiagTailX0RatChunk000Sub000Block166Part020
    + surrogateDiagTailX0RatChunk000Sub000Block166Part021
    + surrogateDiagTailX0RatChunk000Sub000Block166Part022
    + surrogateDiagTailX0RatChunk000Sub000Block166Part023
    + surrogateDiagTailX0RatChunk000Sub000Block166Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block166_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block166Head + surrogateDiagTailX0RatChunk000Sub000Block166Mid + surrogateDiagTailX0RatChunk000Sub000Block166Tail =
      surrogateDiagTailX0RatChunk000Sub000Block166 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block166Head surrogateDiagTailX0RatChunk000Sub000Block166Mid surrogateDiagTailX0RatChunk000Sub000Block166Tail surrogateDiagTailX0RatChunk000Sub000Block166
  ring

def SurrogateDiagonalTailChunk000Sub000Block166HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block166HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block166Head

def SurrogateDiagonalTailChunk000Sub000Block166MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block166MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block166Mid

def SurrogateDiagonalTailChunk000Sub000Block166TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block166TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block166Tail

theorem surrogateDiagonalTailChunk000Sub000Block166_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block166HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block166MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block166TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block166Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block166 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block166HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block166MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block166TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block166Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block166_eq_head_add_mid_add_tail

/-- Block 167 covers tail-support indices [4175,4200) and q from 6919 to 6963. -/

def TailChunk000Sub000Block167Part000SupportExplicit : Finset ℕ :=
  ([6919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part000 : ℚ :=
  (238787599 : ℚ) / 2038839430348800

def SurrogateDiagonalTailChunk000Sub000Block167Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6919
    = surrogateDiagTailX0RatChunk000Sub000Block167Part000

theorem surrogateDiagonalTailChunk000Sub000Block167Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part000] using hcert

def TailChunk000Sub000Block167Part001SupportExplicit : Finset ℕ :=
  ([6922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part001 : ℚ :=
  (299463025 : ℚ) / 143347870401312

def SurrogateDiagonalTailChunk000Sub000Block167Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6922
    = surrogateDiagTailX0RatChunk000Sub000Block167Part001

theorem surrogateDiagonalTailChunk000Sub000Block167Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part001] using hcert

def TailChunk000Sub000Block167Part002SupportExplicit : Finset ℕ :=
  ([6923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part002 : ℚ :=
  (27262476575 : ℚ) / 168729768097938432

def SurrogateDiagonalTailChunk000Sub000Block167Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6923
    = surrogateDiagTailX0RatChunk000Sub000Block167Part002

theorem surrogateDiagonalTailChunk000Sub000Block167Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part002] using hcert

def TailChunk000Sub000Block167Part003SupportExplicit : Finset ℕ :=
  ([6926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part003 : ℚ :=
  (187380765625 : ℚ) / 89799748781694642

def SurrogateDiagonalTailChunk000Sub000Block167Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6926
    = surrogateDiagTailX0RatChunk000Sub000Block167Part003

theorem surrogateDiagonalTailChunk000Sub000Block167Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part003] using hcert

def TailChunk000Sub000Block167Part004SupportExplicit : Finset ℕ :=
  ([6927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part004 : ℚ :=
  (333174861275 : ℚ) / 567623103410217984

def SurrogateDiagonalTailChunk000Sub000Block167Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6927
    = surrogateDiagTailX0RatChunk000Sub000Block167Part004

theorem surrogateDiagonalTailChunk000Sub000Block167Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part004] using hcert

def TailChunk000Sub000Block167Part005SupportExplicit : Finset ℕ :=
  ([6931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part005 : ℚ :=
  (235908975 : ℚ) / 14676670193062528

def SurrogateDiagonalTailChunk000Sub000Block167Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6931
    = surrogateDiagTailX0RatChunk000Sub000Block167Part005

theorem surrogateDiagonalTailChunk000Sub000Block167Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part005] using hcert

def TailChunk000Sub000Block167Part006SupportExplicit : Finset ℕ :=
  ([6933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part006 : ℚ :=
  (13350079829 : ℚ) / 22783726402113600

def SurrogateDiagonalTailChunk000Sub000Block167Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6933
    = surrogateDiagTailX0RatChunk000Sub000Block167Part006

theorem surrogateDiagonalTailChunk000Sub000Block167Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part006] using hcert

def TailChunk000Sub000Block167Part007SupportExplicit : Finset ℕ :=
  ([6934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part007 : ℚ :=
  (187813890625 : ℚ) / 90215487664845042

def SurrogateDiagonalTailChunk000Sub000Block167Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6934
    = surrogateDiagTailX0RatChunk000Sub000Block167Part007

theorem surrogateDiagonalTailChunk000Sub000Block167Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part007] using hcert

def TailChunk000Sub000Block167Part008SupportExplicit : Finset ℕ :=
  ([6935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part008 : ℚ :=
  (530597981575 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub000Block167Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6935
    = surrogateDiagTailX0RatChunk000Sub000Block167Part008

theorem surrogateDiagonalTailChunk000Sub000Block167Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part008] using hcert

def TailChunk000Sub000Block167Part009SupportExplicit : Finset ℕ :=
  ([6937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part009 : ℚ :=
  (12316419091 : ℚ) / 124518141544579200

def SurrogateDiagonalTailChunk000Sub000Block167Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6937
    = surrogateDiagTailX0RatChunk000Sub000Block167Part009

theorem surrogateDiagonalTailChunk000Sub000Block167Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part009] using hcert

def TailChunk000Sub000Block167Part010SupportExplicit : Finset ℕ :=
  ([6938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part010 : ℚ :=
  (188030640625 : ℚ) / 90423897598647072

def SurrogateDiagonalTailChunk000Sub000Block167Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6938
    = surrogateDiagTailX0RatChunk000Sub000Block167Part010

theorem surrogateDiagonalTailChunk000Sub000Block167Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part010] using hcert

def TailChunk000Sub000Block167Part011SupportExplicit : Finset ℕ :=
  ([6941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part011 : ℚ :=
  (2683982089 : ℚ) / 52520371974000000

def SurrogateDiagonalTailChunk000Sub000Block167Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6941
    = surrogateDiagTailX0RatChunk000Sub000Block167Part011

theorem surrogateDiagonalTailChunk000Sub000Block167Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part011] using hcert

def TailChunk000Sub000Block167Part012SupportExplicit : Finset ℕ :=
  ([6942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part012 : ℚ :=
  (547181433475 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block167Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6942
    = surrogateDiagTailX0RatChunk000Sub000Block167Part012

theorem surrogateDiagonalTailChunk000Sub000Block167Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part012] using hcert

def TailChunk000Sub000Block167Part013SupportExplicit : Finset ℕ :=
  ([6943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part013 : ℚ :=
  (1123880951 : ℚ) / 104434414994457600

def SurrogateDiagonalTailChunk000Sub000Block167Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6943
    = surrogateDiagTailX0RatChunk000Sub000Block167Part013

theorem surrogateDiagonalTailChunk000Sub000Block167Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part013] using hcert

def TailChunk000Sub000Block167Part014SupportExplicit : Finset ℕ :=
  ([6945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part014 : ℚ :=
  (251706789275 : ℚ) / 77768452785881088

def SurrogateDiagonalTailChunk000Sub000Block167Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6945
    = surrogateDiagTailX0RatChunk000Sub000Block167Part014

theorem surrogateDiagonalTailChunk000Sub000Block167Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part014] using hcert

def TailChunk000Sub000Block167Part015SupportExplicit : Finset ℕ :=
  ([6946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part015 : ℚ :=
  (14118782323 : ℚ) / 2965395460500000

def SurrogateDiagonalTailChunk000Sub000Block167Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6946
    = surrogateDiagTailX0RatChunk000Sub000Block167Part015

theorem surrogateDiagonalTailChunk000Sub000Block167Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part015] using hcert

def TailChunk000Sub000Block167Part016SupportExplicit : Finset ℕ :=
  ([6947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part016 : ℚ :=
  (754075140625 : ℚ) / 1455144035307348882

def SurrogateDiagonalTailChunk000Sub000Block167Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6947
    = surrogateDiagTailX0RatChunk000Sub000Block167Part016

theorem surrogateDiagonalTailChunk000Sub000Block167Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part016] using hcert

def TailChunk000Sub000Block167Part017SupportExplicit : Finset ℕ :=
  ([6949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part017 : ℚ :=
  (754509390625 : ℚ) / 1456820709810545952

def SurrogateDiagonalTailChunk000Sub000Block167Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6949
    = surrogateDiagTailX0RatChunk000Sub000Block167Part017

theorem surrogateDiagonalTailChunk000Sub000Block167Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part017] using hcert

def TailChunk000Sub000Block167Part018SupportExplicit : Finset ℕ :=
  ([6951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part018 : ℚ :=
  (27984600197 : ℚ) / 12298088053785600

def SurrogateDiagonalTailChunk000Sub000Block167Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6951
    = surrogateDiagTailX0RatChunk000Sub000Block167Part018

theorem surrogateDiagonalTailChunk000Sub000Block167Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part018] using hcert

def TailChunk000Sub000Block167Part019SupportExplicit : Finset ℕ :=
  ([6953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part019 : ℚ :=
  (695838410275 : ℚ) / 1135239387081080832

def SurrogateDiagonalTailChunk000Sub000Block167Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6953
    = surrogateDiagTailX0RatChunk000Sub000Block167Part019

theorem surrogateDiagonalTailChunk000Sub000Block167Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part019] using hcert

def TailChunk000Sub000Block167Part020SupportExplicit : Finset ℕ :=
  ([6954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part020 : ℚ :=
  (6196497203 : ℚ) / 435443538493440

def SurrogateDiagonalTailChunk000Sub000Block167Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6954
    = surrogateDiagTailX0RatChunk000Sub000Block167Part020

theorem surrogateDiagonalTailChunk000Sub000Block167Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part020] using hcert

def TailChunk000Sub000Block167Part021SupportExplicit : Finset ℕ :=
  ([6955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part021 : ℚ :=
  (1025517041375 : ℚ) / 837886655584272384

def SurrogateDiagonalTailChunk000Sub000Block167Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6955
    = surrogateDiagTailX0RatChunk000Sub000Block167Part021

theorem surrogateDiagonalTailChunk000Sub000Block167Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part021] using hcert

def TailChunk000Sub000Block167Part022SupportExplicit : Finset ℕ :=
  ([6959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part022 : ℚ :=
  (756682515625 : ℚ) / 1465225826972890962

def SurrogateDiagonalTailChunk000Sub000Block167Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6959
    = surrogateDiagTailX0RatChunk000Sub000Block167Part022

theorem surrogateDiagonalTailChunk000Sub000Block167Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part022] using hcert

def TailChunk000Sub000Block167Part023SupportExplicit : Finset ℕ :=
  ([6961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part023 : ℚ :=
  (1211388025 : ℚ) / 2347057928282112

def SurrogateDiagonalTailChunk000Sub000Block167Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6961
    = surrogateDiagTailX0RatChunk000Sub000Block167Part023

theorem surrogateDiagonalTailChunk000Sub000Block167Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part023] using hcert

def TailChunk000Sub000Block167Part024SupportExplicit : Finset ℕ :=
  ([6963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part024 : ℚ :=
  (1670117359 : ℚ) / 864532872000000

def SurrogateDiagonalTailChunk000Sub000Block167Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6963
    = surrogateDiagTailX0RatChunk000Sub000Block167Part024

theorem surrogateDiagonalTailChunk000Sub000Block167Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block167HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block167Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block167Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block167Part000
    + surrogateDiagTailX0RatChunk000Sub000Block167Part001
    + surrogateDiagTailX0RatChunk000Sub000Block167Part002
    + surrogateDiagTailX0RatChunk000Sub000Block167Part003
    + surrogateDiagTailX0RatChunk000Sub000Block167Part004
    + surrogateDiagTailX0RatChunk000Sub000Block167Part005
    + surrogateDiagTailX0RatChunk000Sub000Block167Part006
    + surrogateDiagTailX0RatChunk000Sub000Block167Part007
    + surrogateDiagTailX0RatChunk000Sub000Block167Part008
    + surrogateDiagTailX0RatChunk000Sub000Block167Part009

def surrogateDiagonalTailChunk000Sub000Block167MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block167Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block167Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block167Part010
    + surrogateDiagTailX0RatChunk000Sub000Block167Part011
    + surrogateDiagTailX0RatChunk000Sub000Block167Part012
    + surrogateDiagTailX0RatChunk000Sub000Block167Part013
    + surrogateDiagTailX0RatChunk000Sub000Block167Part014
    + surrogateDiagTailX0RatChunk000Sub000Block167Part015
    + surrogateDiagTailX0RatChunk000Sub000Block167Part016
    + surrogateDiagTailX0RatChunk000Sub000Block167Part017
    + surrogateDiagTailX0RatChunk000Sub000Block167Part018
    + surrogateDiagTailX0RatChunk000Sub000Block167Part019

def surrogateDiagonalTailChunk000Sub000Block167TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block167Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block167Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block167Part020
    + surrogateDiagTailX0RatChunk000Sub000Block167Part021
    + surrogateDiagTailX0RatChunk000Sub000Block167Part022
    + surrogateDiagTailX0RatChunk000Sub000Block167Part023
    + surrogateDiagTailX0RatChunk000Sub000Block167Part024

def surrogateDiagonalTailChunk000Sub000Block167Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block167HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block167MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block167TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block167 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block167Part000
    + surrogateDiagTailX0RatChunk000Sub000Block167Part001
    + surrogateDiagTailX0RatChunk000Sub000Block167Part002
    + surrogateDiagTailX0RatChunk000Sub000Block167Part003
    + surrogateDiagTailX0RatChunk000Sub000Block167Part004
    + surrogateDiagTailX0RatChunk000Sub000Block167Part005
    + surrogateDiagTailX0RatChunk000Sub000Block167Part006
    + surrogateDiagTailX0RatChunk000Sub000Block167Part007
    + surrogateDiagTailX0RatChunk000Sub000Block167Part008
    + surrogateDiagTailX0RatChunk000Sub000Block167Part009
    + surrogateDiagTailX0RatChunk000Sub000Block167Part010
    + surrogateDiagTailX0RatChunk000Sub000Block167Part011
    + surrogateDiagTailX0RatChunk000Sub000Block167Part012
    + surrogateDiagTailX0RatChunk000Sub000Block167Part013
    + surrogateDiagTailX0RatChunk000Sub000Block167Part014
    + surrogateDiagTailX0RatChunk000Sub000Block167Part015
    + surrogateDiagTailX0RatChunk000Sub000Block167Part016
    + surrogateDiagTailX0RatChunk000Sub000Block167Part017
    + surrogateDiagTailX0RatChunk000Sub000Block167Part018
    + surrogateDiagTailX0RatChunk000Sub000Block167Part019
    + surrogateDiagTailX0RatChunk000Sub000Block167Part020
    + surrogateDiagTailX0RatChunk000Sub000Block167Part021
    + surrogateDiagTailX0RatChunk000Sub000Block167Part022
    + surrogateDiagTailX0RatChunk000Sub000Block167Part023
    + surrogateDiagTailX0RatChunk000Sub000Block167Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block167_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block167Head + surrogateDiagTailX0RatChunk000Sub000Block167Mid + surrogateDiagTailX0RatChunk000Sub000Block167Tail =
      surrogateDiagTailX0RatChunk000Sub000Block167 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block167Head surrogateDiagTailX0RatChunk000Sub000Block167Mid surrogateDiagTailX0RatChunk000Sub000Block167Tail surrogateDiagTailX0RatChunk000Sub000Block167
  ring

def SurrogateDiagonalTailChunk000Sub000Block167HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block167HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block167Head

def SurrogateDiagonalTailChunk000Sub000Block167MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block167MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block167Mid

def SurrogateDiagonalTailChunk000Sub000Block167TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block167TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block167Tail

theorem surrogateDiagonalTailChunk000Sub000Block167_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block167HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block167MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block167TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block167Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block167 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block167HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block167MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block167TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block167Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block167_eq_head_add_mid_add_tail

/-- Block 168 covers tail-support indices [4200,4225) and q from 6965 to 7001. -/

def TailChunk000Sub000Block168Part000SupportExplicit : Finset ℕ :=
  ([6965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part000 : ℚ :=
  (941125364225 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub000Block168Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6965
    = surrogateDiagTailX0RatChunk000Sub000Block168Part000

theorem surrogateDiagonalTailChunk000Sub000Block168Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part000] using hcert

def TailChunk000Sub000Block168Part001SupportExplicit : Finset ℕ :=
  ([6967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part001 : ℚ :=
  (758423265625 : ℚ) / 1471976064360813042

def SurrogateDiagonalTailChunk000Sub000Block168Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6967
    = surrogateDiagTailX0RatChunk000Sub000Block168Part001

theorem surrogateDiagonalTailChunk000Sub000Block168Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part001] using hcert

def TailChunk000Sub000Block168Part002SupportExplicit : Finset ℕ :=
  ([6969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part002 : ℚ :=
  (31687998581 : ℚ) / 18744228096000000

def SurrogateDiagonalTailChunk000Sub000Block168Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6969
    = surrogateDiagTailX0RatChunk000Sub000Block168Part002

theorem surrogateDiagonalTailChunk000Sub000Block168Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part002] using hcert

def TailChunk000Sub000Block168Part003SupportExplicit : Finset ℕ :=
  ([6970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part003 : ℚ :=
  (6289643893 : ℚ) / 1073956572364800

def SurrogateDiagonalTailChunk000Sub000Block168Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6970
    = surrogateDiagTailX0RatChunk000Sub000Block168Part003

theorem surrogateDiagonalTailChunk000Sub000Block168Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part003] using hcert

def TailChunk000Sub000Block168Part004SupportExplicit : Finset ℕ :=
  ([6971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part004 : ℚ :=
  (1214871025 : ℚ) / 2360575865578962

def SurrogateDiagonalTailChunk000Sub000Block168Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6971
    = surrogateDiagTailX0RatChunk000Sub000Block168Part004

theorem surrogateDiagonalTailChunk000Sub000Block168Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part004] using hcert

def TailChunk000Sub000Block168Part005SupportExplicit : Finset ℕ :=
  ([6973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part005 : ℚ :=
  (78543672175 : ℚ) / 130839453091526688

def SurrogateDiagonalTailChunk000Sub000Block168Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6973
    = surrogateDiagTailX0RatChunk000Sub000Block168Part005

theorem surrogateDiagonalTailChunk000Sub000Block168Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part005] using hcert

def TailChunk000Sub000Block168Part006SupportExplicit : Finset ℕ :=
  ([6974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part006 : ℚ :=
  (1153517269 : ℚ) / 398928599205888

def SurrogateDiagonalTailChunk000Sub000Block168Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6974
    = surrogateDiagTailX0RatChunk000Sub000Block168Part006

theorem surrogateDiagonalTailChunk000Sub000Block168Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part006] using hcert

def TailChunk000Sub000Block168Part007SupportExplicit : Finset ℕ :=
  ([6977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part007 : ℚ :=
  (760602015625 : ℚ) / 1480446628407017472

def SurrogateDiagonalTailChunk000Sub000Block168Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6977
    = surrogateDiagTailX0RatChunk000Sub000Block168Part007

theorem surrogateDiagonalTailChunk000Sub000Block168Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part007] using hcert

def TailChunk000Sub000Block168Part008SupportExplicit : Finset ℕ :=
  ([6978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part008 : ℚ :=
  (675814145875 : ℚ) / 72940939652316288

def SurrogateDiagonalTailChunk000Sub000Block168Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6978
    = surrogateDiagTailX0RatChunk000Sub000Block168Part008

theorem surrogateDiagonalTailChunk000Sub000Block168Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part008] using hcert

def TailChunk000Sub000Block168Part009SupportExplicit : Finset ℕ :=
  ([6979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part009 : ℚ :=
  (2482358469775 : ℚ) / 3189107905431717888

def SurrogateDiagonalTailChunk000Sub000Block168Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6979
    = surrogateDiagTailX0RatChunk000Sub000Block168Part009

theorem surrogateDiagonalTailChunk000Sub000Block168Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part009] using hcert

def TailChunk000Sub000Block168Part010SupportExplicit : Finset ℕ :=
  ([6981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part010 : ℚ :=
  (302628645175 : ℚ) / 138803553493106688

def SurrogateDiagonalTailChunk000Sub000Block168Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6981
    = surrogateDiagTailX0RatChunk000Sub000Block168Part010

theorem surrogateDiagonalTailChunk000Sub000Block168Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part010] using hcert

def TailChunk000Sub000Block168Part011SupportExplicit : Finset ℕ :=
  ([6982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part011 : ℚ :=
  (304677025 : ℚ) / 148384506977202

def SurrogateDiagonalTailChunk000Sub000Block168Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6982
    = surrogateDiagTailX0RatChunk000Sub000Block168Part011

theorem surrogateDiagonalTailChunk000Sub000Block168Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part011] using hcert

def TailChunk000Sub000Block168Part012SupportExplicit : Finset ℕ :=
  ([6983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part012 : ℚ :=
  (761910765625 : ℚ) / 1485546482892211122

def SurrogateDiagonalTailChunk000Sub000Block168Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6983
    = surrogateDiagTailX0RatChunk000Sub000Block168Part012

theorem surrogateDiagonalTailChunk000Sub000Block168Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part012] using hcert

def TailChunk000Sub000Block168Part013SupportExplicit : Finset ℕ :=
  ([6985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part013 : ℚ :=
  (83141297 : ℚ) / 65854115389440

def SurrogateDiagonalTailChunk000Sub000Block168Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6985
    = surrogateDiagTailX0RatChunk000Sub000Block168Part013

theorem surrogateDiagonalTailChunk000Sub000Block168Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part013] using hcert

def TailChunk000Sub000Block168Part014SupportExplicit : Finset ℕ :=
  ([6986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part014 : ℚ :=
  (77721650125 : ℚ) / 22146582676609152

def SurrogateDiagonalTailChunk000Sub000Block168Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6986
    = surrogateDiagTailX0RatChunk000Sub000Block168Part014

theorem surrogateDiagonalTailChunk000Sub000Block168Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part014] using hcert

def TailChunk000Sub000Block168Part015SupportExplicit : Finset ℕ :=
  ([6987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part015 : ℚ :=
  (522812583525 : ℚ) / 298993089601601536

def SurrogateDiagonalTailChunk000Sub000Block168Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6987
    = surrogateDiagTailX0RatChunk000Sub000Block168Part015

theorem surrogateDiagonalTailChunk000Sub000Block168Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part015] using hcert

def TailChunk000Sub000Block168Part016SupportExplicit : Finset ℕ :=
  ([6989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part016 : ℚ :=
  (3226236761 : ℚ) / 5665802629939200

def SurrogateDiagonalTailChunk000Sub000Block168Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6989
    = surrogateDiagTailX0RatChunk000Sub000Block168Part016

theorem surrogateDiagonalTailChunk000Sub000Block168Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part016] using hcert

def TailChunk000Sub000Block168Part017SupportExplicit : Finset ℕ :=
  ([6990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part017 : ℚ :=
  (500452321525 : ℚ) / 29671448377294848

def SurrogateDiagonalTailChunk000Sub000Block168Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6990
    = surrogateDiagTailX0RatChunk000Sub000Block168Part017

theorem surrogateDiagonalTailChunk000Sub000Block168Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part017] using hcert

def TailChunk000Sub000Block168Part018SupportExplicit : Finset ℕ :=
  ([6991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part018 : ℚ :=
  (1221852025 : ℚ) / 2387786833884402

def SurrogateDiagonalTailChunk000Sub000Block168Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6991
    = surrogateDiagTailX0RatChunk000Sub000Block168Part018

theorem surrogateDiagonalTailChunk000Sub000Block168Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part018] using hcert

def TailChunk000Sub000Block168Part019SupportExplicit : Finset ℕ :=
  ([6994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part019 : ℚ :=
  (1373109880375 : ℚ) / 267479818102407168

def SurrogateDiagonalTailChunk000Sub000Block168Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6994
    = surrogateDiagTailX0RatChunk000Sub000Block168Part019

theorem surrogateDiagonalTailChunk000Sub000Block168Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part019] using hcert

def TailChunk000Sub000Block168Part020SupportExplicit : Finset ℕ :=
  ([6995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part020 : ℚ :=
  (2200296785425 : ℚ) / 2445093717897627648

def SurrogateDiagonalTailChunk000Sub000Block168Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6995
    = surrogateDiagTailX0RatChunk000Sub000Block168Part020

theorem surrogateDiagonalTailChunk000Sub000Block168Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part020] using hcert

def TailChunk000Sub000Block168Part021SupportExplicit : Finset ℕ :=
  ([6997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part021 : ℚ :=
  (764968890625 : ℚ) / 1497497378467936032

def SurrogateDiagonalTailChunk000Sub000Block168Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6997
    = surrogateDiagTailX0RatChunk000Sub000Block168Part021

theorem surrogateDiagonalTailChunk000Sub000Block168Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part021] using hcert

def TailChunk000Sub000Block168Part022SupportExplicit : Finset ℕ :=
  ([6998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part022 : ℚ :=
  (1530069049975 : ℚ) / 374374344616984008

def SurrogateDiagonalTailChunk000Sub000Block168Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6998
    = surrogateDiagTailX0RatChunk000Sub000Block168Part022

theorem surrogateDiagonalTailChunk000Sub000Block168Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part022] using hcert

def TailChunk000Sub000Block168Part023SupportExplicit : Finset ℕ :=
  ([6999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part023 : ℚ :=
  (850170895175 : ℚ) / 591603902604616704

def SurrogateDiagonalTailChunk000Sub000Block168Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6999
    = surrogateDiagTailX0RatChunk000Sub000Block168Part023

theorem surrogateDiagonalTailChunk000Sub000Block168Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part023] using hcert

def TailChunk000Sub000Block168Part024SupportExplicit : Finset ℕ :=
  ([7001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block168Part024 : ℚ :=
  (49014001 : ℚ) / 96059208000000

def SurrogateDiagonalTailChunk000Sub000Block168Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7001
    = surrogateDiagTailX0RatChunk000Sub000Block168Part024

theorem surrogateDiagonalTailChunk000Sub000Block168Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block168Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block168Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block168Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block168Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block168Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block168Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block168HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block168Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block168Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block168Part000
    + surrogateDiagTailX0RatChunk000Sub000Block168Part001
    + surrogateDiagTailX0RatChunk000Sub000Block168Part002
    + surrogateDiagTailX0RatChunk000Sub000Block168Part003
    + surrogateDiagTailX0RatChunk000Sub000Block168Part004
    + surrogateDiagTailX0RatChunk000Sub000Block168Part005
    + surrogateDiagTailX0RatChunk000Sub000Block168Part006
    + surrogateDiagTailX0RatChunk000Sub000Block168Part007
    + surrogateDiagTailX0RatChunk000Sub000Block168Part008
    + surrogateDiagTailX0RatChunk000Sub000Block168Part009

def surrogateDiagonalTailChunk000Sub000Block168MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block168Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block168Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block168Part010
    + surrogateDiagTailX0RatChunk000Sub000Block168Part011
    + surrogateDiagTailX0RatChunk000Sub000Block168Part012
    + surrogateDiagTailX0RatChunk000Sub000Block168Part013
    + surrogateDiagTailX0RatChunk000Sub000Block168Part014
    + surrogateDiagTailX0RatChunk000Sub000Block168Part015
    + surrogateDiagTailX0RatChunk000Sub000Block168Part016
    + surrogateDiagTailX0RatChunk000Sub000Block168Part017
    + surrogateDiagTailX0RatChunk000Sub000Block168Part018
    + surrogateDiagTailX0RatChunk000Sub000Block168Part019

def surrogateDiagonalTailChunk000Sub000Block168TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block168Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block168Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block168Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block168Part020
    + surrogateDiagTailX0RatChunk000Sub000Block168Part021
    + surrogateDiagTailX0RatChunk000Sub000Block168Part022
    + surrogateDiagTailX0RatChunk000Sub000Block168Part023
    + surrogateDiagTailX0RatChunk000Sub000Block168Part024

def surrogateDiagonalTailChunk000Sub000Block168Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block168HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block168MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block168TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block168 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block168Part000
    + surrogateDiagTailX0RatChunk000Sub000Block168Part001
    + surrogateDiagTailX0RatChunk000Sub000Block168Part002
    + surrogateDiagTailX0RatChunk000Sub000Block168Part003
    + surrogateDiagTailX0RatChunk000Sub000Block168Part004
    + surrogateDiagTailX0RatChunk000Sub000Block168Part005
    + surrogateDiagTailX0RatChunk000Sub000Block168Part006
    + surrogateDiagTailX0RatChunk000Sub000Block168Part007
    + surrogateDiagTailX0RatChunk000Sub000Block168Part008
    + surrogateDiagTailX0RatChunk000Sub000Block168Part009
    + surrogateDiagTailX0RatChunk000Sub000Block168Part010
    + surrogateDiagTailX0RatChunk000Sub000Block168Part011
    + surrogateDiagTailX0RatChunk000Sub000Block168Part012
    + surrogateDiagTailX0RatChunk000Sub000Block168Part013
    + surrogateDiagTailX0RatChunk000Sub000Block168Part014
    + surrogateDiagTailX0RatChunk000Sub000Block168Part015
    + surrogateDiagTailX0RatChunk000Sub000Block168Part016
    + surrogateDiagTailX0RatChunk000Sub000Block168Part017
    + surrogateDiagTailX0RatChunk000Sub000Block168Part018
    + surrogateDiagTailX0RatChunk000Sub000Block168Part019
    + surrogateDiagTailX0RatChunk000Sub000Block168Part020
    + surrogateDiagTailX0RatChunk000Sub000Block168Part021
    + surrogateDiagTailX0RatChunk000Sub000Block168Part022
    + surrogateDiagTailX0RatChunk000Sub000Block168Part023
    + surrogateDiagTailX0RatChunk000Sub000Block168Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block168_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block168Head + surrogateDiagTailX0RatChunk000Sub000Block168Mid + surrogateDiagTailX0RatChunk000Sub000Block168Tail =
      surrogateDiagTailX0RatChunk000Sub000Block168 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block168Head surrogateDiagTailX0RatChunk000Sub000Block168Mid surrogateDiagTailX0RatChunk000Sub000Block168Tail surrogateDiagTailX0RatChunk000Sub000Block168
  ring

def SurrogateDiagonalTailChunk000Sub000Block168HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block168HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block168Head

def SurrogateDiagonalTailChunk000Sub000Block168MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block168MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block168Mid

def SurrogateDiagonalTailChunk000Sub000Block168TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block168TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block168Tail

theorem surrogateDiagonalTailChunk000Sub000Block168_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block168HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block168MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block168TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block168Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block168 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block168HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block168MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block168TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block168Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block168_eq_head_add_mid_add_tail

/-- Block 169 covers tail-support indices [4225,4250) and q from 7003 to 7043. -/

def TailChunk000Sub000Block169Part000SupportExplicit : Finset ℕ :=
  ([7003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part000 : ℚ :=
  (985571511675 : ℚ) / 1790539031274428416

def SurrogateDiagonalTailChunk000Sub000Block169Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7003
    = surrogateDiagTailX0RatChunk000Sub000Block169Part000

theorem surrogateDiagonalTailChunk000Sub000Block169Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part000] using hcert

def TailChunk000Sub000Block169Part001SupportExplicit : Finset ℕ :=
  ([7005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part001 : ℚ :=
  (222132821475 : ℚ) / 80496912523378688

def SurrogateDiagonalTailChunk000Sub000Block169Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7005
    = surrogateDiagTailX0RatChunk000Sub000Block169Part001

theorem surrogateDiagonalTailChunk000Sub000Block169Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part001] using hcert

def TailChunk000Sub000Block169Part002SupportExplicit : Finset ℕ :=
  ([7006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part002 : ℚ :=
  (14543997841 : ℚ) / 3187013979340800

def SurrogateDiagonalTailChunk000Sub000Block169Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7006
    = surrogateDiagTailX0RatChunk000Sub000Block169Part002

theorem surrogateDiagonalTailChunk000Sub000Block169Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part002] using hcert

def TailChunk000Sub000Block169Part003SupportExplicit : Finset ℕ :=
  ([7009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part003 : ℚ :=
  (46924534075 : ℚ) / 85063555054429056

def SurrogateDiagonalTailChunk000Sub000Block169Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7009
    = surrogateDiagTailX0RatChunk000Sub000Block169Part003

theorem surrogateDiagonalTailChunk000Sub000Block169Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part003] using hcert

def TailChunk000Sub000Block169Part004SupportExplicit : Finset ℕ :=
  ([7010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part004 : ℚ :=
  (45381819589 : ℚ) / 6147789312000000

def SurrogateDiagonalTailChunk000Sub000Block169Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7010
    = surrogateDiagTailX0RatChunk000Sub000Block169Part004

theorem surrogateDiagonalTailChunk000Sub000Block169Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part004] using hcert

def TailChunk000Sub000Block169Part005SupportExplicit : Finset ℕ :=
  ([7013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part005 : ℚ :=
  (768471390625 : ℚ) / 1511243678551010592

def SurrogateDiagonalTailChunk000Sub000Block169Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7013
    = surrogateDiagTailX0RatChunk000Sub000Block169Part005

theorem surrogateDiagonalTailChunk000Sub000Block169Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part005] using hcert

def TailChunk000Sub000Block169Part006SupportExplicit : Finset ℕ :=
  ([7014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part006 : ℚ :=
  (261111511325 : ℚ) / 19685851268097024

def SurrogateDiagonalTailChunk000Sub000Block169Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7014
    = surrogateDiagTailX0RatChunk000Sub000Block169Part006

theorem surrogateDiagonalTailChunk000Sub000Block169Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part006] using hcert

def TailChunk000Sub000Block169Part007SupportExplicit : Finset ℕ :=
  ([7015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part007 : ℚ :=
  (2839729861 : ℚ) / 12956010459955200

def SurrogateDiagonalTailChunk000Sub000Block169Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7015
    = surrogateDiagTailX0RatChunk000Sub000Block169Part007

theorem surrogateDiagonalTailChunk000Sub000Block169Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part007] using hcert

def TailChunk000Sub000Block169Part008SupportExplicit : Finset ℕ :=
  ([7017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part008 : ℚ :=
  (341884367525 : ℚ) / 597715988644590144

def SurrogateDiagonalTailChunk000Sub000Block169Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7017
    = surrogateDiagTailX0RatChunk000Sub000Block169Part008

theorem surrogateDiagonalTailChunk000Sub000Block169Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part008] using hcert

def TailChunk000Sub000Block169Part009SupportExplicit : Finset ℕ :=
  ([7019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block169Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7019
    = surrogateDiagTailX0RatChunk000Sub000Block169Part009

theorem surrogateDiagonalTailChunk000Sub000Block169Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part009] using hcert

def TailChunk000Sub000Block169Part010SupportExplicit : Finset ℕ :=
  ([7021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part010 : ℚ :=
  (14959087625 : ℚ) / 89014345131884544

def SurrogateDiagonalTailChunk000Sub000Block169Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7021
    = surrogateDiagTailX0RatChunk000Sub000Block169Part010

theorem surrogateDiagonalTailChunk000Sub000Block169Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part010] using hcert

def TailChunk000Sub000Block169Part011SupportExplicit : Finset ℕ :=
  ([7022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part011 : ℚ :=
  (308178025 : ℚ) / 151815220982802

def SurrogateDiagonalTailChunk000Sub000Block169Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7022
    = surrogateDiagTailX0RatChunk000Sub000Block169Part011

theorem surrogateDiagonalTailChunk000Sub000Block169Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part011] using hcert

def TailChunk000Sub000Block169Part012SupportExplicit : Finset ℕ :=
  ([7023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part012 : ℚ :=
  (13698760019 : ℚ) / 23990553439257600

def SurrogateDiagonalTailChunk000Sub000Block169Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7023
    = surrogateDiagTailX0RatChunk000Sub000Block169Part012

theorem surrogateDiagonalTailChunk000Sub000Block169Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part012] using hcert

def TailChunk000Sub000Block169Part013SupportExplicit : Finset ℕ :=
  ([7026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part013 : ℚ :=
  (5481144623 : ℚ) / 599763835981440

def SurrogateDiagonalTailChunk000Sub000Block169Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7026
    = surrogateDiagTailX0RatChunk000Sub000Block169Part013

theorem surrogateDiagonalTailChunk000Sub000Block169Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part013] using hcert

def TailChunk000Sub000Block169Part014SupportExplicit : Finset ℕ :=
  ([7027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block169Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7027
    = surrogateDiagTailX0RatChunk000Sub000Block169Part014

theorem surrogateDiagonalTailChunk000Sub000Block169Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part014] using hcert

def TailChunk000Sub000Block169Part015SupportExplicit : Finset ℕ :=
  ([7030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part015 : ℚ :=
  (641260305625 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block169Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7030
    = surrogateDiagTailX0RatChunk000Sub000Block169Part015

theorem surrogateDiagonalTailChunk000Sub000Block169Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part015] using hcert

def TailChunk000Sub000Block169Part016SupportExplicit : Finset ℕ :=
  ([7031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part016 : ℚ :=
  (2863362625 : ℚ) / 308363845622317056

def SurrogateDiagonalTailChunk000Sub000Block169Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7031
    = surrogateDiagTailX0RatChunk000Sub000Block169Part016

theorem surrogateDiagonalTailChunk000Sub000Block169Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part016] using hcert

def TailChunk000Sub000Block169Part017SupportExplicit : Finset ℕ :=
  ([7033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part017 : ℚ :=
  (6700586659 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block169Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7033
    = surrogateDiagTailX0RatChunk000Sub000Block169Part017

theorem surrogateDiagonalTailChunk000Sub000Block169Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part017] using hcert

def TailChunk000Sub000Block169Part018SupportExplicit : Finset ℕ :=
  ([7034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part018 : ℚ :=
  (193270140625 : ℚ) / 95534961552636192

def SurrogateDiagonalTailChunk000Sub000Block169Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7034
    = surrogateDiagTailX0RatChunk000Sub000Block169Part018

theorem surrogateDiagonalTailChunk000Sub000Block169Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part018] using hcert

def TailChunk000Sub000Block169Part019SupportExplicit : Finset ℕ :=
  ([7035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part019 : ℚ :=
  (215018890525 : ℚ) / 83954947780509696

def SurrogateDiagonalTailChunk000Sub000Block169Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7035
    = surrogateDiagTailX0RatChunk000Sub000Block169Part019

theorem surrogateDiagonalTailChunk000Sub000Block169Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part019] using hcert

def TailChunk000Sub000Block169Part020SupportExplicit : Finset ℕ :=
  ([7037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part020 : ℚ :=
  (3171691567 : ℚ) / 211351641731971200

def SurrogateDiagonalTailChunk000Sub000Block169Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7037
    = surrogateDiagTailX0RatChunk000Sub000Block169Part020

theorem surrogateDiagonalTailChunk000Sub000Block169Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part020] using hcert

def TailChunk000Sub000Block169Part021SupportExplicit : Finset ℕ :=
  ([7039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block169Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7039
    = surrogateDiagTailX0RatChunk000Sub000Block169Part021

theorem surrogateDiagonalTailChunk000Sub000Block169Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part021] using hcert

def TailChunk000Sub000Block169Part022SupportExplicit : Finset ℕ :=
  ([7041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part022 : ℚ :=
  (344225898725 : ℚ) / 605938959732354624

def SurrogateDiagonalTailChunk000Sub000Block169Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7041
    = surrogateDiagTailX0RatChunk000Sub000Block169Part022

theorem surrogateDiagonalTailChunk000Sub000Block169Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part022] using hcert

def TailChunk000Sub000Block169Part023SupportExplicit : Finset ℕ :=
  ([7042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part023 : ℚ :=
  (695009088925 : ℚ) / 205800643790218368

def SurrogateDiagonalTailChunk000Sub000Block169Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7042
    = surrogateDiagTailX0RatChunk000Sub000Block169Part023

theorem surrogateDiagonalTailChunk000Sub000Block169Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part023] using hcert

def TailChunk000Sub000Block169Part024SupportExplicit : Finset ℕ :=
  ([7043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part024 : ℚ :=
  (775060140625 : ℚ) / 1537272826571506962

def SurrogateDiagonalTailChunk000Sub000Block169Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7043
    = surrogateDiagTailX0RatChunk000Sub000Block169Part024

theorem surrogateDiagonalTailChunk000Sub000Block169Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block169HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block169Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block169Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block169Part000
    + surrogateDiagTailX0RatChunk000Sub000Block169Part001
    + surrogateDiagTailX0RatChunk000Sub000Block169Part002
    + surrogateDiagTailX0RatChunk000Sub000Block169Part003
    + surrogateDiagTailX0RatChunk000Sub000Block169Part004
    + surrogateDiagTailX0RatChunk000Sub000Block169Part005
    + surrogateDiagTailX0RatChunk000Sub000Block169Part006
    + surrogateDiagTailX0RatChunk000Sub000Block169Part007
    + surrogateDiagTailX0RatChunk000Sub000Block169Part008
    + surrogateDiagTailX0RatChunk000Sub000Block169Part009

def surrogateDiagonalTailChunk000Sub000Block169MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block169Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block169Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block169Part010
    + surrogateDiagTailX0RatChunk000Sub000Block169Part011
    + surrogateDiagTailX0RatChunk000Sub000Block169Part012
    + surrogateDiagTailX0RatChunk000Sub000Block169Part013
    + surrogateDiagTailX0RatChunk000Sub000Block169Part014
    + surrogateDiagTailX0RatChunk000Sub000Block169Part015
    + surrogateDiagTailX0RatChunk000Sub000Block169Part016
    + surrogateDiagTailX0RatChunk000Sub000Block169Part017
    + surrogateDiagTailX0RatChunk000Sub000Block169Part018
    + surrogateDiagTailX0RatChunk000Sub000Block169Part019

def surrogateDiagonalTailChunk000Sub000Block169TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block169Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block169Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block169Part020
    + surrogateDiagTailX0RatChunk000Sub000Block169Part021
    + surrogateDiagTailX0RatChunk000Sub000Block169Part022
    + surrogateDiagTailX0RatChunk000Sub000Block169Part023
    + surrogateDiagTailX0RatChunk000Sub000Block169Part024

def surrogateDiagonalTailChunk000Sub000Block169Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block169HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block169MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block169TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block169 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block169Part000
    + surrogateDiagTailX0RatChunk000Sub000Block169Part001
    + surrogateDiagTailX0RatChunk000Sub000Block169Part002
    + surrogateDiagTailX0RatChunk000Sub000Block169Part003
    + surrogateDiagTailX0RatChunk000Sub000Block169Part004
    + surrogateDiagTailX0RatChunk000Sub000Block169Part005
    + surrogateDiagTailX0RatChunk000Sub000Block169Part006
    + surrogateDiagTailX0RatChunk000Sub000Block169Part007
    + surrogateDiagTailX0RatChunk000Sub000Block169Part008
    + surrogateDiagTailX0RatChunk000Sub000Block169Part009
    + surrogateDiagTailX0RatChunk000Sub000Block169Part010
    + surrogateDiagTailX0RatChunk000Sub000Block169Part011
    + surrogateDiagTailX0RatChunk000Sub000Block169Part012
    + surrogateDiagTailX0RatChunk000Sub000Block169Part013
    + surrogateDiagTailX0RatChunk000Sub000Block169Part014
    + surrogateDiagTailX0RatChunk000Sub000Block169Part015
    + surrogateDiagTailX0RatChunk000Sub000Block169Part016
    + surrogateDiagTailX0RatChunk000Sub000Block169Part017
    + surrogateDiagTailX0RatChunk000Sub000Block169Part018
    + surrogateDiagTailX0RatChunk000Sub000Block169Part019
    + surrogateDiagTailX0RatChunk000Sub000Block169Part020
    + surrogateDiagTailX0RatChunk000Sub000Block169Part021
    + surrogateDiagTailX0RatChunk000Sub000Block169Part022
    + surrogateDiagTailX0RatChunk000Sub000Block169Part023
    + surrogateDiagTailX0RatChunk000Sub000Block169Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block169_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block169Head + surrogateDiagTailX0RatChunk000Sub000Block169Mid + surrogateDiagTailX0RatChunk000Sub000Block169Tail =
      surrogateDiagTailX0RatChunk000Sub000Block169 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block169Head surrogateDiagTailX0RatChunk000Sub000Block169Mid surrogateDiagTailX0RatChunk000Sub000Block169Tail surrogateDiagTailX0RatChunk000Sub000Block169
  ring

def SurrogateDiagonalTailChunk000Sub000Block169HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block169HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block169Head

def SurrogateDiagonalTailChunk000Sub000Block169MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block169MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block169Mid

def SurrogateDiagonalTailChunk000Sub000Block169TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block169TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block169Tail

theorem surrogateDiagonalTailChunk000Sub000Block169_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block169HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block169MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block169TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block169Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block169 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block169HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block169MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block169TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block169Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block169_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
