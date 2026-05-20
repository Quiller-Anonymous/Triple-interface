import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [142,143). -/

/- Block 142 covers tail-support indices [3550,3575) and q from 5894 to 5935. -/

def TailChunk000Sub000Block142Part000SupportExplicit : Finset ℕ :=
  ([5894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part000 : ℚ :=
  (18121831421 : ℚ) / 2016782283801600

def SurrogateDiagonalTailChunk000Sub000Block142Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5894
    = surrogateDiagTailX0RatChunk000Sub000Block142Part000

theorem surrogateDiagonalTailChunk000Sub000Block142Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part000] using hcert

def TailChunk000Sub000Block142Part001SupportExplicit : Finset ℕ :=
  ([5897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part001 : ℚ :=
  (543353265625 : ℚ) / 755434416828191232

def SurrogateDiagonalTailChunk000Sub000Block142Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5897
    = surrogateDiagTailX0RatChunk000Sub000Block142Part001

theorem surrogateDiagonalTailChunk000Sub000Block142Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part001] using hcert

def TailChunk000Sub000Block142Part002SupportExplicit : Finset ℕ :=
  ([5898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part002 : ℚ :=
  (663717828325 : ℚ) / 37204270445255808

def SurrogateDiagonalTailChunk000Sub000Block142Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5898
    = surrogateDiagTailX0RatChunk000Sub000Block142Part002

theorem surrogateDiagonalTailChunk000Sub000Block142Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part002] using hcert

def TailChunk000Sub000Block142Part003SupportExplicit : Finset ℕ :=
  ([5899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part003 : ℚ :=
  (1012793888825 : ℚ) / 1174305754327547904

def SurrogateDiagonalTailChunk000Sub000Block142Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5899
    = surrogateDiagTailX0RatChunk000Sub000Block142Part003

theorem surrogateDiagonalTailChunk000Sub000Block142Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part003] using hcert

def TailChunk000Sub000Block142Part004SupportExplicit : Finset ℕ :=
  ([5901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part004 : ℚ :=
  (41511794041 : ℚ) / 12748055917363200

def SurrogateDiagonalTailChunk000Sub000Block142Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5901
    = surrogateDiagTailX0RatChunk000Sub000Block142Part004

theorem surrogateDiagonalTailChunk000Sub000Block142Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part004] using hcert

def TailChunk000Sub000Block142Part005SupportExplicit : Finset ℕ :=
  ([5902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part005 : ℚ :=
  (493567212125 : ℚ) / 67632525354230784

def SurrogateDiagonalTailChunk000Sub000Block142Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5902
    = surrogateDiagTailX0RatChunk000Sub000Block142Part005

theorem surrogateDiagonalTailChunk000Sub000Block142Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part005] using hcert

def TailChunk000Sub000Block142Part006SupportExplicit : Finset ℕ :=
  ([5903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part006 : ℚ :=
  (544459515625 : ℚ) / 758514152263963602

def SurrogateDiagonalTailChunk000Sub000Block142Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5903
    = surrogateDiagTailX0RatChunk000Sub000Block142Part006

theorem surrogateDiagonalTailChunk000Sub000Block142Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part006] using hcert

def TailChunk000Sub000Block142Part007SupportExplicit : Finset ℕ :=
  ([5905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part007 : ℚ :=
  (33100768817 : ℚ) / 24821318599065600

def SurrogateDiagonalTailChunk000Sub000Block142Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5905
    = surrogateDiagTailX0RatChunk000Sub000Block142Part007

theorem surrogateDiagonalTailChunk000Sub000Block142Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part007] using hcert

def TailChunk000Sub000Block142Part008SupportExplicit : Finset ℕ :=
  ([5906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part008 : ℚ :=
  (1089808119775 : ℚ) / 189885705058142208

def SurrogateDiagonalTailChunk000Sub000Block142Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5906
    = surrogateDiagTailX0RatChunk000Sub000Block142Part008

theorem surrogateDiagonalTailChunk000Sub000Block142Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part008] using hcert

def TailChunk000Sub000Block142Part009SupportExplicit : Finset ℕ :=
  ([5907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part009 : ℚ :=
  (17222154039 : ℚ) / 5355075366246400

def SurrogateDiagonalTailChunk000Sub000Block142Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5907
    = surrogateDiagTailX0RatChunk000Sub000Block142Part009

theorem surrogateDiagonalTailChunk000Sub000Block142Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part009] using hcert

def TailChunk000Sub000Block142Part010SupportExplicit : Finset ℕ :=
  ([5909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part010 : ℚ :=
  (81684672271 : ℚ) / 96966930004099200

def SurrogateDiagonalTailChunk000Sub000Block142Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5909
    = surrogateDiagTailX0RatChunk000Sub000Block142Part010

theorem surrogateDiagonalTailChunk000Sub000Block142Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part010] using hcert

def TailChunk000Sub000Block142Part011SupportExplicit : Finset ℕ :=
  ([5910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part011 : ℚ :=
  (102075340525 : ℚ) / 3778775587356672

def SurrogateDiagonalTailChunk000Sub000Block142Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5910
    = surrogateDiagTailX0RatChunk000Sub000Block142Part011

theorem surrogateDiagonalTailChunk000Sub000Block142Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part011] using hcert

def TailChunk000Sub000Block142Part012SupportExplicit : Finset ℕ :=
  ([5911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part012 : ℚ :=
  (687807670575 : ℚ) / 838602569386295296

def SurrogateDiagonalTailChunk000Sub000Block142Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5911
    = surrogateDiagTailX0RatChunk000Sub000Block142Part012

theorem surrogateDiagonalTailChunk000Sub000Block142Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part012] using hcert

def TailChunk000Sub000Block142Part013SupportExplicit : Finset ℕ :=
  ([5914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part013 : ℚ :=
  (136622640625 : ℚ) / 47729247403252512

def SurrogateDiagonalTailChunk000Sub000Block142Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5914
    = surrogateDiagTailX0RatChunk000Sub000Block142Part013

theorem surrogateDiagonalTailChunk000Sub000Block142Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part013] using hcert

def TailChunk000Sub000Block142Part014SupportExplicit : Finset ℕ :=
  ([5917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part014 : ℚ :=
  (1697536037 : ℚ) / 2201946584776704

def SurrogateDiagonalTailChunk000Sub000Block142Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5917
    = surrogateDiagTailX0RatChunk000Sub000Block142Part014

theorem surrogateDiagonalTailChunk000Sub000Block142Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part014] using hcert

def TailChunk000Sub000Block142Part015SupportExplicit : Finset ℕ :=
  ([5918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part015 : ℚ :=
  (19548293957 : ℚ) / 2579859356697600

def SurrogateDiagonalTailChunk000Sub000Block142Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5918
    = surrogateDiagTailX0RatChunk000Sub000Block142Part015

theorem surrogateDiagonalTailChunk000Sub000Block142Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part015] using hcert

def TailChunk000Sub000Block142Part016SupportExplicit : Finset ℕ :=
  ([5919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part016 : ℚ :=
  (608032163675 : ℚ) / 302513310537114624

def SurrogateDiagonalTailChunk000Sub000Block142Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5919
    = surrogateDiagTailX0RatChunk000Sub000Block142Part016

theorem surrogateDiagonalTailChunk000Sub000Block142Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part016] using hcert

def TailChunk000Sub000Block142Part017SupportExplicit : Finset ℕ :=
  ([5921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part017 : ℚ :=
  (16773918509 : ℚ) / 21116224400400000

def SurrogateDiagonalTailChunk000Sub000Block142Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5921
    = surrogateDiagTailX0RatChunk000Sub000Block142Part017

theorem surrogateDiagonalTailChunk000Sub000Block142Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part017] using hcert

def TailChunk000Sub000Block142Part018SupportExplicit : Finset ℕ :=
  ([5923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part018 : ℚ :=
  (548155140625 : ℚ) / 768847983703380882

def SurrogateDiagonalTailChunk000Sub000Block142Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5923
    = surrogateDiagTailX0RatChunk000Sub000Block142Part018

theorem surrogateDiagonalTailChunk000Sub000Block142Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part018] using hcert

def TailChunk000Sub000Block142Part019SupportExplicit : Finset ℕ :=
  ([5926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part019 : ℚ :=
  (1097201640775 : ℚ) / 192471785712650568

def SurrogateDiagonalTailChunk000Sub000Block142Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5926
    = surrogateDiagTailX0RatChunk000Sub000Block142Part019

theorem surrogateDiagonalTailChunk000Sub000Block142Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part019] using hcert

def TailChunk000Sub000Block142Part020SupportExplicit : Finset ℕ :=
  ([5927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part020 : ℚ :=
  (548895765625 : ℚ) / 770927355021686322

def SurrogateDiagonalTailChunk000Sub000Block142Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5927
    = surrogateDiagTailX0RatChunk000Sub000Block142Part020

theorem surrogateDiagonalTailChunk000Sub000Block142Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part020] using hcert

def TailChunk000Sub000Block142Part021SupportExplicit : Finset ℕ :=
  ([5930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part021 : ℚ :=
  (277916627025 : ℚ) / 26207910463799296

def SurrogateDiagonalTailChunk000Sub000Block142Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5930
    = surrogateDiagTailX0RatChunk000Sub000Block142Part021

theorem surrogateDiagonalTailChunk000Sub000Block142Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part021] using hcert

def TailChunk000Sub000Block142Part022SupportExplicit : Finset ℕ :=
  ([5933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part022 : ℚ :=
  (680478934075 : ℚ) / 801129106186960896

def SurrogateDiagonalTailChunk000Sub000Block142Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5933
    = surrogateDiagTailX0RatChunk000Sub000Block142Part022

theorem surrogateDiagonalTailChunk000Sub000Block142Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part022] using hcert

def TailChunk000Sub000Block142Part023SupportExplicit : Finset ℕ :=
  ([5934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part023 : ℚ :=
  (89288364925 : ℚ) / 4166167113529344

def SurrogateDiagonalTailChunk000Sub000Block142Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5934
    = surrogateDiagTailX0RatChunk000Sub000Block142Part023

theorem surrogateDiagonalTailChunk000Sub000Block142Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part023] using hcert

def TailChunk000Sub000Block142Part024SupportExplicit : Finset ℕ :=
  ([5935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block142Part024 : ℚ :=
  (208987423175 : ℚ) / 158312640774195456

def SurrogateDiagonalTailChunk000Sub000Block142Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5935
    = surrogateDiagTailX0RatChunk000Sub000Block142Part024

theorem surrogateDiagonalTailChunk000Sub000Block142Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block142Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block142Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block142Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block142Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block142Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block142Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block142HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block142Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block142Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block142Part000
    + surrogateDiagTailX0RatChunk000Sub000Block142Part001
    + surrogateDiagTailX0RatChunk000Sub000Block142Part002
    + surrogateDiagTailX0RatChunk000Sub000Block142Part003
    + surrogateDiagTailX0RatChunk000Sub000Block142Part004
    + surrogateDiagTailX0RatChunk000Sub000Block142Part005
    + surrogateDiagTailX0RatChunk000Sub000Block142Part006
    + surrogateDiagTailX0RatChunk000Sub000Block142Part007
    + surrogateDiagTailX0RatChunk000Sub000Block142Part008
    + surrogateDiagTailX0RatChunk000Sub000Block142Part009

def surrogateDiagonalTailChunk000Sub000Block142MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block142Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block142Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block142Part010
    + surrogateDiagTailX0RatChunk000Sub000Block142Part011
    + surrogateDiagTailX0RatChunk000Sub000Block142Part012
    + surrogateDiagTailX0RatChunk000Sub000Block142Part013
    + surrogateDiagTailX0RatChunk000Sub000Block142Part014
    + surrogateDiagTailX0RatChunk000Sub000Block142Part015
    + surrogateDiagTailX0RatChunk000Sub000Block142Part016
    + surrogateDiagTailX0RatChunk000Sub000Block142Part017
    + surrogateDiagTailX0RatChunk000Sub000Block142Part018
    + surrogateDiagTailX0RatChunk000Sub000Block142Part019

def surrogateDiagonalTailChunk000Sub000Block142TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block142Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block142Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block142Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block142Part020
    + surrogateDiagTailX0RatChunk000Sub000Block142Part021
    + surrogateDiagTailX0RatChunk000Sub000Block142Part022
    + surrogateDiagTailX0RatChunk000Sub000Block142Part023
    + surrogateDiagTailX0RatChunk000Sub000Block142Part024

def surrogateDiagonalTailChunk000Sub000Block142Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block142HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block142MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block142TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block142 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block142Part000
    + surrogateDiagTailX0RatChunk000Sub000Block142Part001
    + surrogateDiagTailX0RatChunk000Sub000Block142Part002
    + surrogateDiagTailX0RatChunk000Sub000Block142Part003
    + surrogateDiagTailX0RatChunk000Sub000Block142Part004
    + surrogateDiagTailX0RatChunk000Sub000Block142Part005
    + surrogateDiagTailX0RatChunk000Sub000Block142Part006
    + surrogateDiagTailX0RatChunk000Sub000Block142Part007
    + surrogateDiagTailX0RatChunk000Sub000Block142Part008
    + surrogateDiagTailX0RatChunk000Sub000Block142Part009
    + surrogateDiagTailX0RatChunk000Sub000Block142Part010
    + surrogateDiagTailX0RatChunk000Sub000Block142Part011
    + surrogateDiagTailX0RatChunk000Sub000Block142Part012
    + surrogateDiagTailX0RatChunk000Sub000Block142Part013
    + surrogateDiagTailX0RatChunk000Sub000Block142Part014
    + surrogateDiagTailX0RatChunk000Sub000Block142Part015
    + surrogateDiagTailX0RatChunk000Sub000Block142Part016
    + surrogateDiagTailX0RatChunk000Sub000Block142Part017
    + surrogateDiagTailX0RatChunk000Sub000Block142Part018
    + surrogateDiagTailX0RatChunk000Sub000Block142Part019
    + surrogateDiagTailX0RatChunk000Sub000Block142Part020
    + surrogateDiagTailX0RatChunk000Sub000Block142Part021
    + surrogateDiagTailX0RatChunk000Sub000Block142Part022
    + surrogateDiagTailX0RatChunk000Sub000Block142Part023
    + surrogateDiagTailX0RatChunk000Sub000Block142Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block142_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block142Head + surrogateDiagTailX0RatChunk000Sub000Block142Mid + surrogateDiagTailX0RatChunk000Sub000Block142Tail =
      surrogateDiagTailX0RatChunk000Sub000Block142 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block142Head surrogateDiagTailX0RatChunk000Sub000Block142Mid surrogateDiagTailX0RatChunk000Sub000Block142Tail surrogateDiagTailX0RatChunk000Sub000Block142
  ring

def SurrogateDiagonalTailChunk000Sub000Block142HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block142HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block142Head

def SurrogateDiagonalTailChunk000Sub000Block142MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block142MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block142Mid

def SurrogateDiagonalTailChunk000Sub000Block142TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block142TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block142Tail

theorem surrogateDiagonalTailChunk000Sub000Block142_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block142HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block142MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block142TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block142Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block142 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block142HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block142MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block142TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block142Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block142_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
