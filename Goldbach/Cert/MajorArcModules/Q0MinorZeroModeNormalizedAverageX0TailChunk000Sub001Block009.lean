import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [9,10). -/

/-- Block 009 covers tail-support indices [5225,5250) and q from 8641 to 8682. -/

def TailChunk000Sub001Block009Part000SupportExplicit : Finset ℕ :=
  ([8641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part000 : ℚ :=
  (1866672025 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub001Block009Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8641
    = surrogateDiagTailX0RatChunk000Sub001Block009Part000

theorem surrogateDiagonalTailChunk000Sub001Block009Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part000] using hcert

def TailChunk000Sub001Block009Part001SupportExplicit : Finset ℕ :=
  ([8642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part001 : ℚ :=
  (187895080425 : ℚ) / 122900767624183808

def SurrogateDiagonalTailChunk000Sub001Block009Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8642
    = surrogateDiagTailX0RatChunk000Sub001Block009Part001

theorem surrogateDiagonalTailChunk000Sub001Block009Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part001] using hcert

def TailChunk000Sub001Block009Part002SupportExplicit : Finset ℕ :=
  ([8643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part002 : ℚ :=
  (2466959499475 : ℚ) / 2362216753371138048

def SurrogateDiagonalTailChunk000Sub001Block009Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8643
    = surrogateDiagTailX0RatChunk000Sub001Block009Part002

theorem surrogateDiagonalTailChunk000Sub001Block009Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part002] using hcert

def TailChunk000Sub001Block009Part003SupportExplicit : Finset ℕ :=
  ([8645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part003 : ℚ :=
  (1136025889625 : ℚ) / 902935721419997184

def SurrogateDiagonalTailChunk000Sub001Block009Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8645
    = surrogateDiagTailX0RatChunk000Sub001Block009Part003

theorem surrogateDiagonalTailChunk000Sub001Block009Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part003] using hcert

def TailChunk000Sub001Block009Part004SupportExplicit : Finset ℕ :=
  ([8646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part004 : ℚ :=
  (8165033203 : ℚ) / 1142668488000000

def SurrogateDiagonalTailChunk000Sub001Block009Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8646
    = surrogateDiagTailX0RatChunk000Sub001Block009Part004

theorem surrogateDiagonalTailChunk000Sub001Block009Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part004] using hcert

def TailChunk000Sub001Block009Part005SupportExplicit : Finset ℕ :=
  ([8647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part005 : ℚ :=
  (1168290765625 : ℚ) / 3493234915404034482

def SurrogateDiagonalTailChunk000Sub001Block009Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8647
    = surrogateDiagTailX0RatChunk000Sub001Block009Part005

theorem surrogateDiagonalTailChunk000Sub001Block009Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part005] using hcert

def TailChunk000Sub001Block009Part006SupportExplicit : Finset ℕ :=
  ([8651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part006 : ℚ :=
  (640933381 : ℚ) / 1778467622400000

def SurrogateDiagonalTailChunk000Sub001Block009Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8651
    = surrogateDiagTailX0RatChunk000Sub001Block009Part006

theorem surrogateDiagonalTailChunk000Sub001Block009Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part006] using hcert

def TailChunk000Sub001Block009Part007SupportExplicit : Finset ℕ :=
  ([8653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part007 : ℚ :=
  (4279863503875 : ℚ) / 10913439334665289728

def SurrogateDiagonalTailChunk000Sub001Block009Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8653
    = surrogateDiagTailX0RatChunk000Sub001Block009Part007

theorem surrogateDiagonalTailChunk000Sub001Block009Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part007] using hcert

def TailChunk000Sub001Block009Part008SupportExplicit : Finset ℕ :=
  ([8654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part008 : ℚ :=
  (292545765625 : ℚ) / 218933856893385522

def SurrogateDiagonalTailChunk000Sub001Block009Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8654
    = surrogateDiagTailX0RatChunk000Sub001Block009Part008

theorem surrogateDiagonalTailChunk000Sub001Block009Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part008] using hcert

def TailChunk000Sub001Block009Part009SupportExplicit : Finset ℕ :=
  ([8655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part009 : ℚ :=
  (107290207675 : ℚ) / 62633147300315136

def SurrogateDiagonalTailChunk000Sub001Block009Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8655
    = surrogateDiagTailX0RatChunk000Sub001Block009Part009

theorem surrogateDiagonalTailChunk000Sub001Block009Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part009] using hcert

def TailChunk000Sub001Block009Part010SupportExplicit : Finset ℕ :=
  ([8657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part010 : ℚ :=
  (8116051769 : ℚ) / 19087411599776160

def SurrogateDiagonalTailChunk000Sub001Block009Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8657
    = surrogateDiagTailX0RatChunk000Sub001Block009Part010

theorem surrogateDiagonalTailChunk000Sub001Block009Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part010] using hcert

def TailChunk000Sub001Block009Part011SupportExplicit : Finset ℕ :=
  ([8659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part011 : ℚ :=
  (207011316875 : ℚ) / 420177931097342976

def SurrogateDiagonalTailChunk000Sub001Block009Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8659
    = surrogateDiagTailX0RatChunk000Sub001Block009Part011

theorem surrogateDiagonalTailChunk000Sub001Block009Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part011] using hcert

def TailChunk000Sub001Block009Part012SupportExplicit : Finset ℕ :=
  ([8661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part012 : ℚ :=
  (2082873711325 : ℚ) / 2775441952115584128

def SurrogateDiagonalTailChunk000Sub001Block009Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8661
    = surrogateDiagTailX0RatChunk000Sub001Block009Part012

theorem surrogateDiagonalTailChunk000Sub001Block009Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part012] using hcert

def TailChunk000Sub001Block009Part013SupportExplicit : Finset ℕ :=
  ([8662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part013 : ℚ :=
  (1827812299 : ℚ) / 1244927335680000

def SurrogateDiagonalTailChunk000Sub001Block009Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8662
    = surrogateDiagTailX0RatChunk000Sub001Block009Part013

theorem surrogateDiagonalTailChunk000Sub001Block009Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part013] using hcert

def TailChunk000Sub001Block009Part014SupportExplicit : Finset ℕ :=
  ([8663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part014 : ℚ :=
  (1172618265625 : ℚ) / 3519164638876547442

def SurrogateDiagonalTailChunk000Sub001Block009Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8663
    = surrogateDiagTailX0RatChunk000Sub001Block009Part014

theorem surrogateDiagonalTailChunk000Sub001Block009Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part014] using hcert

def TailChunk000Sub001Block009Part015SupportExplicit : Finset ℕ :=
  ([8665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part015 : ℚ :=
  (1125525755775 : ℚ) / 1920158681553534976

def SurrogateDiagonalTailChunk000Sub001Block009Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8665
    = surrogateDiagTailX0RatChunk000Sub001Block009Part015

theorem surrogateDiagonalTailChunk000Sub001Block009Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part015] using hcert

def TailChunk000Sub001Block009Part016SupportExplicit : Finset ℕ :=
  ([8666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part016 : ℚ :=
  (257123353825 : ℚ) / 118175043121127712

def SurrogateDiagonalTailChunk000Sub001Block009Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8666
    = surrogateDiagTailX0RatChunk000Sub001Block009Part016

theorem surrogateDiagonalTailChunk000Sub001Block009Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part016] using hcert

def TailChunk000Sub001Block009Part017SupportExplicit : Finset ℕ :=
  ([8669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part017 : ℚ :=
  (1174243140625 : ℚ) / 3528925404003370272

def SurrogateDiagonalTailChunk000Sub001Block009Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8669
    = surrogateDiagTailX0RatChunk000Sub001Block009Part017

theorem surrogateDiagonalTailChunk000Sub001Block009Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part017] using hcert

def TailChunk000Sub001Block009Part018SupportExplicit : Finset ℕ :=
  ([8671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part018 : ℚ :=
  (1249502846225 : ℚ) / 2488590489148194816

def SurrogateDiagonalTailChunk000Sub001Block009Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8671
    = surrogateDiagTailX0RatChunk000Sub001Block009Part018

theorem surrogateDiagonalTailChunk000Sub001Block009Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part018] using hcert

def TailChunk000Sub001Block009Part019SupportExplicit : Finset ℕ :=
  ([8674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part019 : ℚ :=
  (293899515625 : ℚ) / 220965240713060352

def SurrogateDiagonalTailChunk000Sub001Block009Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8674
    = surrogateDiagTailX0RatChunk000Sub001Block009Part019

theorem surrogateDiagonalTailChunk000Sub001Block009Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part019] using hcert

def TailChunk000Sub001Block009Part020SupportExplicit : Finset ℕ :=
  ([8677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part020 : ℚ :=
  (1176411390625 : ℚ) / 3541971325049847072

def SurrogateDiagonalTailChunk000Sub001Block009Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8677
    = surrogateDiagTailX0RatChunk000Sub001Block009Part020

theorem surrogateDiagonalTailChunk000Sub001Block009Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part020] using hcert

def TailChunk000Sub001Block009Part021SupportExplicit : Finset ℕ :=
  ([8678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part021 : ℚ :=
  (294170640625 : ℚ) / 221373207815615442

def SurrogateDiagonalTailChunk000Sub001Block009Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8678
    = surrogateDiagTailX0RatChunk000Sub001Block009Part021

theorem surrogateDiagonalTailChunk000Sub001Block009Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part021] using hcert

def TailChunk000Sub001Block009Part022SupportExplicit : Finset ℕ :=
  ([8679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part022 : ℚ :=
  (9207612673 : ℚ) / 7540705817195520

def SurrogateDiagonalTailChunk000Sub001Block009Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8679
    = surrogateDiagTailX0RatChunk000Sub001Block009Part022

theorem surrogateDiagonalTailChunk000Sub001Block009Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part022] using hcert

def TailChunk000Sub001Block009Part023SupportExplicit : Finset ℕ :=
  ([8681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part023 : ℚ :=
  (1883994025 : ℚ) / 5677612533207552

def SurrogateDiagonalTailChunk000Sub001Block009Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8681
    = surrogateDiagTailX0RatChunk000Sub001Block009Part023

theorem surrogateDiagonalTailChunk000Sub001Block009Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part023] using hcert

def TailChunk000Sub001Block009Part024SupportExplicit : Finset ℕ :=
  ([8682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block009Part024 : ℚ :=
  (26157275 : ℚ) / 5829239625408

def SurrogateDiagonalTailChunk000Sub001Block009Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8682
    = surrogateDiagTailX0RatChunk000Sub001Block009Part024

theorem surrogateDiagonalTailChunk000Sub001Block009Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block009Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block009Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block009Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block009Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block009Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block009HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block009Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block009Part000
    + surrogateDiagTailX0RatChunk000Sub001Block009Part001
    + surrogateDiagTailX0RatChunk000Sub001Block009Part002
    + surrogateDiagTailX0RatChunk000Sub001Block009Part003
    + surrogateDiagTailX0RatChunk000Sub001Block009Part004
    + surrogateDiagTailX0RatChunk000Sub001Block009Part005
    + surrogateDiagTailX0RatChunk000Sub001Block009Part006
    + surrogateDiagTailX0RatChunk000Sub001Block009Part007
    + surrogateDiagTailX0RatChunk000Sub001Block009Part008
    + surrogateDiagTailX0RatChunk000Sub001Block009Part009

def surrogateDiagonalTailChunk000Sub001Block009MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block009Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block009Part010
    + surrogateDiagTailX0RatChunk000Sub001Block009Part011
    + surrogateDiagTailX0RatChunk000Sub001Block009Part012
    + surrogateDiagTailX0RatChunk000Sub001Block009Part013
    + surrogateDiagTailX0RatChunk000Sub001Block009Part014
    + surrogateDiagTailX0RatChunk000Sub001Block009Part015
    + surrogateDiagTailX0RatChunk000Sub001Block009Part016
    + surrogateDiagTailX0RatChunk000Sub001Block009Part017
    + surrogateDiagTailX0RatChunk000Sub001Block009Part018
    + surrogateDiagTailX0RatChunk000Sub001Block009Part019

def surrogateDiagonalTailChunk000Sub001Block009TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block009Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block009Part020
    + surrogateDiagTailX0RatChunk000Sub001Block009Part021
    + surrogateDiagTailX0RatChunk000Sub001Block009Part022
    + surrogateDiagTailX0RatChunk000Sub001Block009Part023
    + surrogateDiagTailX0RatChunk000Sub001Block009Part024

def surrogateDiagonalTailChunk000Sub001Block009Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block009HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block009MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block009TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block009 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block009Part000
    + surrogateDiagTailX0RatChunk000Sub001Block009Part001
    + surrogateDiagTailX0RatChunk000Sub001Block009Part002
    + surrogateDiagTailX0RatChunk000Sub001Block009Part003
    + surrogateDiagTailX0RatChunk000Sub001Block009Part004
    + surrogateDiagTailX0RatChunk000Sub001Block009Part005
    + surrogateDiagTailX0RatChunk000Sub001Block009Part006
    + surrogateDiagTailX0RatChunk000Sub001Block009Part007
    + surrogateDiagTailX0RatChunk000Sub001Block009Part008
    + surrogateDiagTailX0RatChunk000Sub001Block009Part009
    + surrogateDiagTailX0RatChunk000Sub001Block009Part010
    + surrogateDiagTailX0RatChunk000Sub001Block009Part011
    + surrogateDiagTailX0RatChunk000Sub001Block009Part012
    + surrogateDiagTailX0RatChunk000Sub001Block009Part013
    + surrogateDiagTailX0RatChunk000Sub001Block009Part014
    + surrogateDiagTailX0RatChunk000Sub001Block009Part015
    + surrogateDiagTailX0RatChunk000Sub001Block009Part016
    + surrogateDiagTailX0RatChunk000Sub001Block009Part017
    + surrogateDiagTailX0RatChunk000Sub001Block009Part018
    + surrogateDiagTailX0RatChunk000Sub001Block009Part019
    + surrogateDiagTailX0RatChunk000Sub001Block009Part020
    + surrogateDiagTailX0RatChunk000Sub001Block009Part021
    + surrogateDiagTailX0RatChunk000Sub001Block009Part022
    + surrogateDiagTailX0RatChunk000Sub001Block009Part023
    + surrogateDiagTailX0RatChunk000Sub001Block009Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block009_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block009Head + surrogateDiagTailX0RatChunk000Sub001Block009Mid + surrogateDiagTailX0RatChunk000Sub001Block009Tail =
      surrogateDiagTailX0RatChunk000Sub001Block009 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block009Head surrogateDiagTailX0RatChunk000Sub001Block009Mid surrogateDiagTailX0RatChunk000Sub001Block009Tail surrogateDiagTailX0RatChunk000Sub001Block009
  ring

def SurrogateDiagonalTailChunk000Sub001Block009HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block009HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block009Head

def SurrogateDiagonalTailChunk000Sub001Block009MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block009MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block009Mid

def SurrogateDiagonalTailChunk000Sub001Block009TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block009TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block009Tail

theorem surrogateDiagonalTailChunk000Sub001Block009_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block009HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block009MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block009TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block009Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block009 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block009HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block009MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block009TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block009Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block009_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
