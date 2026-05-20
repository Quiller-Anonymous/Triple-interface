import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [45,46). -/

/- Block 045 covers tail-support indices [1125,1150) and q from 1905 to 1945. -/

def TailChunk000Sub000Block045Part000SupportExplicit : Finset ℕ :=
  ([1905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part000 : ℚ :=
  (3082962425 : ℚ) / 23902604845056

def SurrogateDiagonalTailChunk000Sub000Block045Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1905
    = surrogateDiagTailX0RatChunk000Sub000Block045Part000

theorem surrogateDiagonalTailChunk000Sub000Block045Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part000] using hcert

def TailChunk000Sub000Block045Part001SupportExplicit : Finset ℕ :=
  ([1906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part001 : ℚ :=
  (141794130125 : ℚ) / 1026939022255104

def SurrogateDiagonalTailChunk000Sub000Block045Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1906
    = surrogateDiagTailX0RatChunk000Sub000Block045Part001

theorem surrogateDiagonalTailChunk000Sub000Block045Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part001] using hcert

def TailChunk000Sub000Block045Part002SupportExplicit : Finset ℕ :=
  ([1907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part002 : ℚ :=
  (454490208775 : ℚ) / 33000342255941448

def SurrogateDiagonalTailChunk000Sub000Block045Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1907
    = surrogateDiagTailX0RatChunk000Sub000Block045Part002

theorem surrogateDiagonalTailChunk000Sub000Block045Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part002] using hcert

def TailChunk000Sub000Block045Part003SupportExplicit : Finset ℕ :=
  ([1909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part003 : ℚ :=
  (641047209625 : ℚ) / 26483354364390528

def SurrogateDiagonalTailChunk000Sub000Block045Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1909
    = surrogateDiagTailX0RatChunk000Sub000Block045Part003

theorem surrogateDiagonalTailChunk000Sub000Block045Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part003] using hcert

def TailChunk000Sub000Block045Part004SupportExplicit : Finset ℕ :=
  ([1910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part004 : ℚ :=
  (611123433 : ℚ) / 2224589895680

def SurrogateDiagonalTailChunk000Sub000Block045Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1910
    = surrogateDiagTailX0RatChunk000Sub000Block045Part004

theorem surrogateDiagonalTailChunk000Sub000Block045Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part004] using hcert

def TailChunk000Sub000Block045Part005SupportExplicit : Finset ℕ :=
  ([1913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part005 : ℚ :=
  (457354635775 : ℚ) / 33417842715936768

def SurrogateDiagonalTailChunk000Sub000Block045Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1913
    = surrogateDiagTailX0RatChunk000Sub000Block045Part005

theorem surrogateDiagonalTailChunk000Sub000Block045Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part005] using hcert

def TailChunk000Sub000Block045Part006SupportExplicit : Finset ℕ :=
  ([1914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part006 : ℚ :=
  (6930808093 : ℚ) / 9836462899200

def SurrogateDiagonalTailChunk000Sub000Block045Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1914
    = surrogateDiagTailX0RatChunk000Sub000Block045Part006

theorem surrogateDiagonalTailChunk000Sub000Block045Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part006] using hcert

def TailChunk000Sub000Block045Part007SupportExplicit : Finset ℕ :=
  ([1915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part007 : ℚ :=
  (98370282175 : ℚ) / 3407691606200832

def SurrogateDiagonalTailChunk000Sub000Block045Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1915
    = surrogateDiagTailX0RatChunk000Sub000Block045Part007

theorem surrogateDiagonalTailChunk000Sub000Block045Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part007] using hcert

def TailChunk000Sub000Block045Part008SupportExplicit : Finset ℕ :=
  ([1918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part008 : ℚ :=
  (246981656125 : ℚ) / 1108632213946368

def SurrogateDiagonalTailChunk000Sub000Block045Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1918
    = surrogateDiagTailX0RatChunk000Sub000Block045Part008

theorem surrogateDiagonalTailChunk000Sub000Block045Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part008] using hcert

def TailChunk000Sub000Block045Part009SupportExplicit : Finset ℕ :=
  ([1919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part009 : ℚ :=
  (1713480947 : ℚ) / 69997996800000

def SurrogateDiagonalTailChunk000Sub000Block045Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1919
    = surrogateDiagTailX0RatChunk000Sub000Block045Part009

theorem surrogateDiagonalTailChunk000Sub000Block045Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part009] using hcert

def TailChunk000Sub000Block045Part010SupportExplicit : Finset ℕ :=
  ([1921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part010 : ℚ :=
  (110038074175 : ℚ) / 6446424325619712

def SurrogateDiagonalTailChunk000Sub000Block045Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1921
    = surrogateDiagTailX0RatChunk000Sub000Block045Part010

theorem surrogateDiagonalTailChunk000Sub000Block045Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part010] using hcert

def TailChunk000Sub000Block045Part011SupportExplicit : Finset ℕ :=
  ([1923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part011 : ℚ :=
  (6669717227 : ℚ) / 134244571545600

def SurrogateDiagonalTailChunk000Sub000Block045Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1923
    = surrogateDiagTailX0RatChunk000Sub000Block045Part011

theorem surrogateDiagonalTailChunk000Sub000Block045Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part011] using hcert

def TailChunk000Sub000Block045Part012SupportExplicit : Finset ℕ :=
  ([1927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part012 : ℚ :=
  (4788003 : ℚ) / 207691663360

def SurrogateDiagonalTailChunk000Sub000Block045Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1927
    = surrogateDiagTailX0RatChunk000Sub000Block045Part012

theorem surrogateDiagonalTailChunk000Sub000Block045Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part012] using hcert

def TailChunk000Sub000Block045Part013SupportExplicit : Finset ℕ :=
  ([1929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part013 : ℚ :=
  (90329832775 : ℚ) / 1699131387285792

def SurrogateDiagonalTailChunk000Sub000Block045Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1929
    = surrogateDiagTailX0RatChunk000Sub000Block045Part013

theorem surrogateDiagonalTailChunk000Sub000Block045Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part013] using hcert

def TailChunk000Sub000Block045Part014SupportExplicit : Finset ℕ :=
  ([1930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part014 : ℚ :=
  (233994992125 : ℚ) / 869904823615488

def SurrogateDiagonalTailChunk000Sub000Block045Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1930
    = surrogateDiagTailX0RatChunk000Sub000Block045Part014

theorem surrogateDiagonalTailChunk000Sub000Block045Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part014] using hcert

def TailChunk000Sub000Block045Part015SupportExplicit : Finset ℕ :=
  ([1931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part015 : ℚ :=
  (9318173739 : ℚ) / 462588499533400

def SurrogateDiagonalTailChunk000Sub000Block045Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1931
    = surrogateDiagTailX0RatChunk000Sub000Block045Part015

theorem surrogateDiagonalTailChunk000Sub000Block045Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part015] using hcert

def TailChunk000Sub000Block045Part016SupportExplicit : Finset ℕ :=
  ([1933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part016 : ℚ :=
  (1588007825 : ℚ) / 78998120304768

def SurrogateDiagonalTailChunk000Sub000Block045Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1933
    = surrogateDiagTailX0RatChunk000Sub000Block045Part016

theorem surrogateDiagonalTailChunk000Sub000Block045Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part016] using hcert

def TailChunk000Sub000Block045Part017SupportExplicit : Finset ℕ :=
  ([1934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part017 : ℚ :=
  (145990770125 : ℚ) / 1088692845450084

def SurrogateDiagonalTailChunk000Sub000Block045Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1934
    = surrogateDiagTailX0RatChunk000Sub000Block045Part017

theorem surrogateDiagonalTailChunk000Sub000Block045Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part017] using hcert

def TailChunk000Sub000Block045Part018SupportExplicit : Finset ℕ :=
  ([1937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part018 : ℚ :=
  (110470995625 : ℚ) / 6219260002639872

def SurrogateDiagonalTailChunk000Sub000Block045Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1937
    = surrogateDiagTailX0RatChunk000Sub000Block045Part018

theorem surrogateDiagonalTailChunk000Sub000Block045Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part018] using hcert

def TailChunk000Sub000Block045Part019SupportExplicit : Finset ℕ :=
  ([1938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part019 : ℚ :=
  (32615838425 : ℚ) / 45873887182848

def SurrogateDiagonalTailChunk000Sub000Block045Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1938
    = surrogateDiagTailX0RatChunk000Sub000Block045Part019

theorem surrogateDiagonalTailChunk000Sub000Block045Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part019] using hcert

def TailChunk000Sub000Block045Part020SupportExplicit : Finset ℕ :=
  ([1939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part020 : ℚ :=
  (5440542125 : ℚ) / 174118305977856

def SurrogateDiagonalTailChunk000Sub000Block045Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1939
    = surrogateDiagTailX0RatChunk000Sub000Block045Part020

theorem surrogateDiagonalTailChunk000Sub000Block045Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part020] using hcert

def TailChunk000Sub000Block045Part021SupportExplicit : Finset ℕ :=
  ([1941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part021 : ℚ :=
  (13061937775 : ℚ) / 204926440452672

def SurrogateDiagonalTailChunk000Sub000Block045Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1941
    = surrogateDiagTailX0RatChunk000Sub000Block045Part021

theorem surrogateDiagonalTailChunk000Sub000Block045Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part021] using hcert

def TailChunk000Sub000Block045Part022SupportExplicit : Finset ℕ :=
  ([1942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part022 : ℚ :=
  (941898159 : ℚ) / 5903132457080

def SurrogateDiagonalTailChunk000Sub000Block045Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1942
    = surrogateDiagTailX0RatChunk000Sub000Block045Part022

theorem surrogateDiagonalTailChunk000Sub000Block045Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part022] using hcert

def TailChunk000Sub000Block045Part023SupportExplicit : Finset ℕ :=
  ([1943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part023 : ℚ :=
  (227732364725 : ℚ) / 14581584897352704

def SurrogateDiagonalTailChunk000Sub000Block045Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1943
    = surrogateDiagTailX0RatChunk000Sub000Block045Part023

theorem surrogateDiagonalTailChunk000Sub000Block045Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part023] using hcert

def TailChunk000Sub000Block045Part024SupportExplicit : Finset ℕ :=
  ([1945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block045Part024 : ℚ :=
  (202949669525 : ℚ) / 7253769163259904

def SurrogateDiagonalTailChunk000Sub000Block045Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1945
    = surrogateDiagTailX0RatChunk000Sub000Block045Part024

theorem surrogateDiagonalTailChunk000Sub000Block045Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block045Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block045Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block045Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block045Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block045Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block045Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block045HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block045Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block045Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block045Part000
    + surrogateDiagTailX0RatChunk000Sub000Block045Part001
    + surrogateDiagTailX0RatChunk000Sub000Block045Part002
    + surrogateDiagTailX0RatChunk000Sub000Block045Part003
    + surrogateDiagTailX0RatChunk000Sub000Block045Part004
    + surrogateDiagTailX0RatChunk000Sub000Block045Part005
    + surrogateDiagTailX0RatChunk000Sub000Block045Part006
    + surrogateDiagTailX0RatChunk000Sub000Block045Part007
    + surrogateDiagTailX0RatChunk000Sub000Block045Part008
    + surrogateDiagTailX0RatChunk000Sub000Block045Part009

def surrogateDiagonalTailChunk000Sub000Block045MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block045Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block045Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block045Part010
    + surrogateDiagTailX0RatChunk000Sub000Block045Part011
    + surrogateDiagTailX0RatChunk000Sub000Block045Part012
    + surrogateDiagTailX0RatChunk000Sub000Block045Part013
    + surrogateDiagTailX0RatChunk000Sub000Block045Part014
    + surrogateDiagTailX0RatChunk000Sub000Block045Part015
    + surrogateDiagTailX0RatChunk000Sub000Block045Part016
    + surrogateDiagTailX0RatChunk000Sub000Block045Part017
    + surrogateDiagTailX0RatChunk000Sub000Block045Part018
    + surrogateDiagTailX0RatChunk000Sub000Block045Part019

def surrogateDiagonalTailChunk000Sub000Block045TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block045Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block045Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block045Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block045Part020
    + surrogateDiagTailX0RatChunk000Sub000Block045Part021
    + surrogateDiagTailX0RatChunk000Sub000Block045Part022
    + surrogateDiagTailX0RatChunk000Sub000Block045Part023
    + surrogateDiagTailX0RatChunk000Sub000Block045Part024

def surrogateDiagonalTailChunk000Sub000Block045Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block045HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block045MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block045TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block045 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block045Part000
    + surrogateDiagTailX0RatChunk000Sub000Block045Part001
    + surrogateDiagTailX0RatChunk000Sub000Block045Part002
    + surrogateDiagTailX0RatChunk000Sub000Block045Part003
    + surrogateDiagTailX0RatChunk000Sub000Block045Part004
    + surrogateDiagTailX0RatChunk000Sub000Block045Part005
    + surrogateDiagTailX0RatChunk000Sub000Block045Part006
    + surrogateDiagTailX0RatChunk000Sub000Block045Part007
    + surrogateDiagTailX0RatChunk000Sub000Block045Part008
    + surrogateDiagTailX0RatChunk000Sub000Block045Part009
    + surrogateDiagTailX0RatChunk000Sub000Block045Part010
    + surrogateDiagTailX0RatChunk000Sub000Block045Part011
    + surrogateDiagTailX0RatChunk000Sub000Block045Part012
    + surrogateDiagTailX0RatChunk000Sub000Block045Part013
    + surrogateDiagTailX0RatChunk000Sub000Block045Part014
    + surrogateDiagTailX0RatChunk000Sub000Block045Part015
    + surrogateDiagTailX0RatChunk000Sub000Block045Part016
    + surrogateDiagTailX0RatChunk000Sub000Block045Part017
    + surrogateDiagTailX0RatChunk000Sub000Block045Part018
    + surrogateDiagTailX0RatChunk000Sub000Block045Part019
    + surrogateDiagTailX0RatChunk000Sub000Block045Part020
    + surrogateDiagTailX0RatChunk000Sub000Block045Part021
    + surrogateDiagTailX0RatChunk000Sub000Block045Part022
    + surrogateDiagTailX0RatChunk000Sub000Block045Part023
    + surrogateDiagTailX0RatChunk000Sub000Block045Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block045_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block045Head + surrogateDiagTailX0RatChunk000Sub000Block045Mid + surrogateDiagTailX0RatChunk000Sub000Block045Tail =
      surrogateDiagTailX0RatChunk000Sub000Block045 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block045Head surrogateDiagTailX0RatChunk000Sub000Block045Mid surrogateDiagTailX0RatChunk000Sub000Block045Tail surrogateDiagTailX0RatChunk000Sub000Block045
  ring

def SurrogateDiagonalTailChunk000Sub000Block045HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block045HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block045Head

def SurrogateDiagonalTailChunk000Sub000Block045MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block045MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block045Mid

def SurrogateDiagonalTailChunk000Sub000Block045TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block045TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block045Tail

theorem surrogateDiagonalTailChunk000Sub000Block045_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block045HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block045MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block045TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block045Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block045 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block045HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block045MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block045TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block045Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block045_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
