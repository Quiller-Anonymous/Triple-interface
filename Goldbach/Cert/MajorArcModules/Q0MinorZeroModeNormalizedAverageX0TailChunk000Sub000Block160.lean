import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [160,161). -/

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

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
