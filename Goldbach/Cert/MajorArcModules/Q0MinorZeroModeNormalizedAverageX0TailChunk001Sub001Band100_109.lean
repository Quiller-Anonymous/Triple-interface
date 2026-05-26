import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [100,110). -/

/-- Block 100 covers tail-support indices [17500,17525) and q from 28838 to 28878. -/

def TailChunk001Sub001Block100Part000SupportExplicit : Finset ℕ :=
  ([28838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part000 : ℚ :=
  (3248555640625 : ℚ) / 27013879127904093522

def SurrogateDiagonalTailChunk001Sub001Block100Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28838
    = surrogateDiagTailX0RatChunk001Sub001Block100Part000

theorem surrogateDiagonalTailChunk001Sub001Block100Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part000] using hcert

def TailChunk001Sub001Block100Part001SupportExplicit : Finset ℕ :=
  ([28839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part001 : ℚ :=
  (41675 : ℚ) / 22762700321642496

def SurrogateDiagonalTailChunk001Sub001Block100Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28839
    = surrogateDiagTailX0RatChunk001Sub001Block100Part001

theorem surrogateDiagonalTailChunk001Sub001Block100Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part001] using hcert

def TailChunk001Sub001Block100Part002SupportExplicit : Finset ℕ :=
  ([28841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part002 : ℚ :=
  (4203706669 : ℚ) / 65988201251250000000

def SurrogateDiagonalTailChunk001Sub001Block100Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28841
    = surrogateDiagTailX0RatChunk001Sub001Block100Part002

theorem surrogateDiagonalTailChunk001Sub001Block100Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part002] using hcert

def TailChunk001Sub001Block100Part003SupportExplicit : Finset ℕ :=
  ([28842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part003 : ℚ :=
  (57783859159 : ℚ) / 131179605907046400

def SurrogateDiagonalTailChunk001Sub001Block100Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28842
    = surrogateDiagTailX0RatChunk001Sub001Block100Part003

theorem surrogateDiagonalTailChunk001Sub001Block100Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part003] using hcert

def TailChunk001Sub001Block100Part004SupportExplicit : Finset ℕ :=
  ([28843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block100Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28843
    = surrogateDiagTailX0RatChunk001Sub001Block100Part004

theorem surrogateDiagonalTailChunk001Sub001Block100Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part004] using hcert

def TailChunk001Sub001Block100Part005SupportExplicit : Finset ℕ :=
  ([28846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part005 : ℚ :=
  (3250358265625 : ℚ) / 27043869554246784882

def SurrogateDiagonalTailChunk001Sub001Block100Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28846
    = surrogateDiagTailX0RatChunk001Sub001Block100Part005

theorem surrogateDiagonalTailChunk001Sub001Block100Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part005] using hcert

def TailChunk001Sub001Block100Part006SupportExplicit : Finset ℕ :=
  ([28847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part006 : ℚ :=
  (362958209425 : ℚ) / 167511714520949194752

def SurrogateDiagonalTailChunk001Sub001Block100Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28847
    = surrogateDiagTailX0RatChunk001Sub001Block100Part006

theorem surrogateDiagonalTailChunk001Sub001Block100Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part006] using hcert

def TailChunk001Sub001Block100Part007SupportExplicit : Finset ℕ :=
  ([28849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part007 : ℚ :=
  (11335651425 : ℚ) / 28246779763565264896

def SurrogateDiagonalTailChunk001Sub001Block100Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28849
    = surrogateDiagTailX0RatChunk001Sub001Block100Part007

theorem surrogateDiagonalTailChunk001Sub001Block100Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part007] using hcert

def TailChunk001Sub001Block100Part008SupportExplicit : Finset ℕ :=
  ([28851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part008 : ℚ :=
  (5652764641075 : ℚ) / 311830703116043470848

def SurrogateDiagonalTailChunk001Sub001Block100Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28851
    = surrogateDiagTailX0RatChunk001Sub001Block100Part008

theorem surrogateDiagonalTailChunk001Sub001Block100Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part008] using hcert

def TailChunk001Sub001Block100Part009SupportExplicit : Finset ℕ :=
  ([28853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part009 : ℚ :=
  (8740091849 : ℚ) / 8067129135206400000

def SurrogateDiagonalTailChunk001Sub001Block100Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28853
    = surrogateDiagTailX0RatChunk001Sub001Block100Part009

theorem surrogateDiagonalTailChunk001Sub001Block100Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part009] using hcert

def TailChunk001Sub001Block100Part010SupportExplicit : Finset ℕ :=
  ([28855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part010 : ℚ :=
  (104674959875 : ℚ) / 28796547088714825728

def SurrogateDiagonalTailChunk001Sub001Block100Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28855
    = surrogateDiagTailX0RatChunk001Sub001Block100Part010

theorem surrogateDiagonalTailChunk001Sub001Block100Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part010] using hcert

def TailChunk001Sub001Block100Part011SupportExplicit : Finset ℕ :=
  ([28857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part011 : ℚ :=
  (413017514075 : ℚ) / 24454449840825127872

def SurrogateDiagonalTailChunk001Sub001Block100Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28857
    = surrogateDiagTailX0RatChunk001Sub001Block100Part011

theorem surrogateDiagonalTailChunk001Sub001Block100Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part011] using hcert

def TailChunk001Sub001Block100Part012SupportExplicit : Finset ℕ :=
  ([28858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part012 : ℚ :=
  (35893920425 : ℚ) / 32720703825547149696

def SurrogateDiagonalTailChunk001Sub001Block100Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28858
    = surrogateDiagTailX0RatChunk001Sub001Block100Part012

theorem surrogateDiagonalTailChunk001Sub001Block100Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part012] using hcert

def TailChunk001Sub001Block100Part013SupportExplicit : Finset ℕ :=
  ([28859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block100Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28859
    = surrogateDiagTailX0RatChunk001Sub001Block100Part013

theorem surrogateDiagonalTailChunk001Sub001Block100Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part013] using hcert

def TailChunk001Sub001Block100Part014SupportExplicit : Finset ℕ :=
  ([28862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block100Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28862
    = surrogateDiagTailX0RatChunk001Sub001Block100Part014

theorem surrogateDiagonalTailChunk001Sub001Block100Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part014] using hcert

def TailChunk001Sub001Block100Part015SupportExplicit : Finset ℕ :=
  ([28865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part015 : ℚ :=
  (44459679281 : ℚ) / 11715142560000000000

def SurrogateDiagonalTailChunk001Sub001Block100Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28865
    = surrogateDiagTailX0RatChunk001Sub001Block100Part015

theorem surrogateDiagonalTailChunk001Sub001Block100Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part015] using hcert

def TailChunk001Sub001Block100Part016SupportExplicit : Finset ℕ :=
  ([28866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part016 : ℚ :=
  (1456322880175 : ℚ) / 16581476717206437888

def SurrogateDiagonalTailChunk001Sub001Block100Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28866
    = surrogateDiagTailX0RatChunk001Sub001Block100Part016

theorem surrogateDiagonalTailChunk001Sub001Block100Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part016] using hcert

def TailChunk001Sub001Block100Part017SupportExplicit : Finset ℕ :=
  ([28867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block100Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28867
    = surrogateDiagTailX0RatChunk001Sub001Block100Part017

theorem surrogateDiagonalTailChunk001Sub001Block100Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part017] using hcert

def TailChunk001Sub001Block100Part018SupportExplicit : Finset ℕ :=
  ([28869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part018 : ℚ :=
  (2893527598475 : ℚ) / 171466094556788149824

def SurrogateDiagonalTailChunk001Sub001Block100Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28869
    = surrogateDiagTailX0RatChunk001Sub001Block100Part018

theorem surrogateDiagonalTailChunk001Sub001Block100Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part018] using hcert

def TailChunk001Sub001Block100Part019SupportExplicit : Finset ℕ :=
  ([28870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part019 : ℚ :=
  (14103056125 : ℚ) / 1200191114428360704

def SurrogateDiagonalTailChunk001Sub001Block100Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28870
    = surrogateDiagTailX0RatChunk001Sub001Block100Part019

theorem surrogateDiagonalTailChunk001Sub001Block100Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part019] using hcert

def TailChunk001Sub001Block100Part020SupportExplicit : Finset ℕ :=
  ([28871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block100Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28871
    = surrogateDiagTailX0RatChunk001Sub001Block100Part020

theorem surrogateDiagonalTailChunk001Sub001Block100Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part020] using hcert

def TailChunk001Sub001Block100Part021SupportExplicit : Finset ℕ :=
  ([28873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part021 : ℚ :=
  (2754134441 : ℚ) / 5597334002375884800

def SurrogateDiagonalTailChunk001Sub001Block100Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28873
    = surrogateDiagTailX0RatChunk001Sub001Block100Part021

theorem surrogateDiagonalTailChunk001Sub001Block100Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part021] using hcert

def TailChunk001Sub001Block100Part022SupportExplicit : Finset ℕ :=
  ([28874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block100Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28874
    = surrogateDiagTailX0RatChunk001Sub001Block100Part022

theorem surrogateDiagonalTailChunk001Sub001Block100Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part022] using hcert

def TailChunk001Sub001Block100Part023SupportExplicit : Finset ℕ :=
  ([28877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part023 : ℚ :=
  (1180723529 : ℚ) / 12976764116163661440

def SurrogateDiagonalTailChunk001Sub001Block100Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28877
    = surrogateDiagTailX0RatChunk001Sub001Block100Part023

theorem surrogateDiagonalTailChunk001Sub001Block100Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part023] using hcert

def TailChunk001Sub001Block100Part024SupportExplicit : Finset ℕ :=
  ([28878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block100Part024 : ℚ :=
  (5655601825 : ℚ) / 83793310898357448

def SurrogateDiagonalTailChunk001Sub001Block100Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28878
    = surrogateDiagTailX0RatChunk001Sub001Block100Part024

theorem surrogateDiagonalTailChunk001Sub001Block100Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block100Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block100Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block100Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block100Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block100Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block100Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block100HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block100Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block100Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block100Part000
    + surrogateDiagTailX0RatChunk001Sub001Block100Part001
    + surrogateDiagTailX0RatChunk001Sub001Block100Part002
    + surrogateDiagTailX0RatChunk001Sub001Block100Part003
    + surrogateDiagTailX0RatChunk001Sub001Block100Part004
    + surrogateDiagTailX0RatChunk001Sub001Block100Part005
    + surrogateDiagTailX0RatChunk001Sub001Block100Part006
    + surrogateDiagTailX0RatChunk001Sub001Block100Part007
    + surrogateDiagTailX0RatChunk001Sub001Block100Part008
    + surrogateDiagTailX0RatChunk001Sub001Block100Part009

def surrogateDiagonalTailChunk001Sub001Block100MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block100Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block100Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block100Part010
    + surrogateDiagTailX0RatChunk001Sub001Block100Part011
    + surrogateDiagTailX0RatChunk001Sub001Block100Part012
    + surrogateDiagTailX0RatChunk001Sub001Block100Part013
    + surrogateDiagTailX0RatChunk001Sub001Block100Part014
    + surrogateDiagTailX0RatChunk001Sub001Block100Part015
    + surrogateDiagTailX0RatChunk001Sub001Block100Part016
    + surrogateDiagTailX0RatChunk001Sub001Block100Part017
    + surrogateDiagTailX0RatChunk001Sub001Block100Part018
    + surrogateDiagTailX0RatChunk001Sub001Block100Part019

def surrogateDiagonalTailChunk001Sub001Block100TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block100Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block100Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block100Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block100Part020
    + surrogateDiagTailX0RatChunk001Sub001Block100Part021
    + surrogateDiagTailX0RatChunk001Sub001Block100Part022
    + surrogateDiagTailX0RatChunk001Sub001Block100Part023
    + surrogateDiagTailX0RatChunk001Sub001Block100Part024

def surrogateDiagonalTailChunk001Sub001Block100Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block100HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block100MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block100TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block100 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block100Part000
    + surrogateDiagTailX0RatChunk001Sub001Block100Part001
    + surrogateDiagTailX0RatChunk001Sub001Block100Part002
    + surrogateDiagTailX0RatChunk001Sub001Block100Part003
    + surrogateDiagTailX0RatChunk001Sub001Block100Part004
    + surrogateDiagTailX0RatChunk001Sub001Block100Part005
    + surrogateDiagTailX0RatChunk001Sub001Block100Part006
    + surrogateDiagTailX0RatChunk001Sub001Block100Part007
    + surrogateDiagTailX0RatChunk001Sub001Block100Part008
    + surrogateDiagTailX0RatChunk001Sub001Block100Part009
    + surrogateDiagTailX0RatChunk001Sub001Block100Part010
    + surrogateDiagTailX0RatChunk001Sub001Block100Part011
    + surrogateDiagTailX0RatChunk001Sub001Block100Part012
    + surrogateDiagTailX0RatChunk001Sub001Block100Part013
    + surrogateDiagTailX0RatChunk001Sub001Block100Part014
    + surrogateDiagTailX0RatChunk001Sub001Block100Part015
    + surrogateDiagTailX0RatChunk001Sub001Block100Part016
    + surrogateDiagTailX0RatChunk001Sub001Block100Part017
    + surrogateDiagTailX0RatChunk001Sub001Block100Part018
    + surrogateDiagTailX0RatChunk001Sub001Block100Part019
    + surrogateDiagTailX0RatChunk001Sub001Block100Part020
    + surrogateDiagTailX0RatChunk001Sub001Block100Part021
    + surrogateDiagTailX0RatChunk001Sub001Block100Part022
    + surrogateDiagTailX0RatChunk001Sub001Block100Part023
    + surrogateDiagTailX0RatChunk001Sub001Block100Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block100_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block100Head + surrogateDiagTailX0RatChunk001Sub001Block100Mid + surrogateDiagTailX0RatChunk001Sub001Block100Tail =
      surrogateDiagTailX0RatChunk001Sub001Block100 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block100Head surrogateDiagTailX0RatChunk001Sub001Block100Mid surrogateDiagTailX0RatChunk001Sub001Block100Tail surrogateDiagTailX0RatChunk001Sub001Block100
  ring

def SurrogateDiagonalTailChunk001Sub001Block100HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block100HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block100Head

def SurrogateDiagonalTailChunk001Sub001Block100MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block100MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block100Mid

def SurrogateDiagonalTailChunk001Sub001Block100TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block100TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block100Tail

theorem surrogateDiagonalTailChunk001Sub001Block100_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block100HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block100MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block100TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block100Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block100 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block100HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block100MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block100TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block100Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block100_eq_head_add_mid_add_tail

/-- Block 101 covers tail-support indices [17525,17550) and q from 28879 to 28918. -/

def TailChunk001Sub001Block101Part000SupportExplicit : Finset ℕ :=
  ([28879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block101Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28879
    = surrogateDiagTailX0RatChunk001Sub001Block101Part000

theorem surrogateDiagonalTailChunk001Sub001Block101Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part000] using hcert

def TailChunk001Sub001Block101Part001SupportExplicit : Finset ℕ :=
  ([28882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part001 : ℚ :=
  (266624497175 : ℚ) / 29292504718022028864

def SurrogateDiagonalTailChunk001Sub001Block101Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28882
    = surrogateDiagTailX0RatChunk001Sub001Block101Part001

theorem surrogateDiagonalTailChunk001Sub001Block101Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part001] using hcert

def TailChunk001Sub001Block101Part002SupportExplicit : Finset ℕ :=
  ([28883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part002 : ℚ :=
  (15149541925 : ℚ) / 37840340212290551808

def SurrogateDiagonalTailChunk001Sub001Block101Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28883
    = surrogateDiagTailX0RatChunk001Sub001Block101Part002

theorem surrogateDiagonalTailChunk001Sub001Block101Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part002] using hcert

def TailChunk001Sub001Block101Part003SupportExplicit : Finset ℕ :=
  ([28885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part003 : ℚ :=
  (90322313725 : ℚ) / 26531632859543764992

def SurrogateDiagonalTailChunk001Sub001Block101Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28885
    = surrogateDiagTailX0RatChunk001Sub001Block101Part003

theorem surrogateDiagonalTailChunk001Sub001Block101Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part003] using hcert

def TailChunk001Sub001Block101Part004SupportExplicit : Finset ℕ :=
  ([28886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part004 : ℚ :=
  (26943560707 : ℚ) / 2074014720000000000

def SurrogateDiagonalTailChunk001Sub001Block101Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28886
    = surrogateDiagTailX0RatChunk001Sub001Block101Part004

theorem surrogateDiagonalTailChunk001Sub001Block101Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part004] using hcert

def TailChunk001Sub001Block101Part005SupportExplicit : Finset ℕ :=
  ([28887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part005 : ℚ :=
  (362142121675 : ℚ) / 21486772485726745728

def SurrogateDiagonalTailChunk001Sub001Block101Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28887
    = surrogateDiagTailX0RatChunk001Sub001Block101Part005

theorem surrogateDiagonalTailChunk001Sub001Block101Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part005] using hcert

def TailChunk001Sub001Block101Part006SupportExplicit : Finset ℕ :=
  ([28889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part006 : ℚ :=
  (1065867206125 : ℚ) / 939179825570771307648

def SurrogateDiagonalTailChunk001Sub001Block101Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28889
    = surrogateDiagTailX0RatChunk001Sub001Block101Part006

theorem surrogateDiagonalTailChunk001Sub001Block101Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part006] using hcert

def TailChunk001Sub001Block101Part007SupportExplicit : Finset ℕ :=
  ([28891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part007 : ℚ :=
  (103600839025 : ℚ) / 1661777975338799351808

def SurrogateDiagonalTailChunk001Sub001Block101Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28891
    = surrogateDiagTailX0RatChunk001Sub001Block101Part007

theorem surrogateDiagonalTailChunk001Sub001Block101Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part007] using hcert

def TailChunk001Sub001Block101Part008SupportExplicit : Finset ℕ :=
  ([28893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part008 : ℚ :=
  (23186724787 : ℚ) / 1376296423701491520

def SurrogateDiagonalTailChunk001Sub001Block101Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28893
    = surrogateDiagTailX0RatChunk001Sub001Block101Part008

theorem surrogateDiagonalTailChunk001Sub001Block101Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part008] using hcert

def TailChunk001Sub001Block101Part009SupportExplicit : Finset ℕ :=
  ([28894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block101Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28894
    = surrogateDiagTailX0RatChunk001Sub001Block101Part009

theorem surrogateDiagonalTailChunk001Sub001Block101Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part009] using hcert

def TailChunk001Sub001Block101Part010SupportExplicit : Finset ℕ :=
  ([28895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part010 : ℚ :=
  (2087830715125 : ℚ) / 713472066046853203968

def SurrogateDiagonalTailChunk001Sub001Block101Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28895
    = surrogateDiagTailX0RatChunk001Sub001Block101Part010

theorem surrogateDiagonalTailChunk001Sub001Block101Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part010] using hcert

def TailChunk001Sub001Block101Part011SupportExplicit : Finset ℕ :=
  ([28897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part011 : ℚ :=
  (22129379663 : ℚ) / 20167822838016000000

def SurrogateDiagonalTailChunk001Sub001Block101Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28897
    = surrogateDiagTailX0RatChunk001Sub001Block101Part011

theorem surrogateDiagonalTailChunk001Sub001Block101Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part011] using hcert

def TailChunk001Sub001Block101Part012SupportExplicit : Finset ℕ :=
  ([28898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block101Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28898
    = surrogateDiagTailX0RatChunk001Sub001Block101Part012

theorem surrogateDiagonalTailChunk001Sub001Block101Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part012] using hcert

def TailChunk001Sub001Block101Part013SupportExplicit : Finset ℕ :=
  ([28901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block101Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28901
    = surrogateDiagTailX0RatChunk001Sub001Block101Part013

theorem surrogateDiagonalTailChunk001Sub001Block101Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part013] using hcert

def TailChunk001Sub001Block101Part014SupportExplicit : Finset ℕ :=
  ([28902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part014 : ℚ :=
  (51794323825 : ℚ) / 768660781628522496

def SurrogateDiagonalTailChunk001Sub001Block101Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28902
    = surrogateDiagTailX0RatChunk001Sub001Block101Part014

theorem surrogateDiagonalTailChunk001Sub001Block101Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part014] using hcert

def TailChunk001Sub001Block101Part015SupportExplicit : Finset ℕ :=
  ([28903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part015 : ℚ :=
  (1066898956225 : ℚ) / 941002148247647551488

def SurrogateDiagonalTailChunk001Sub001Block101Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28903
    = surrogateDiagTailX0RatChunk001Sub001Block101Part015

theorem surrogateDiagonalTailChunk001Sub001Block101Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part015] using hcert

def TailChunk001Sub001Block101Part016SupportExplicit : Finset ℕ :=
  ([28905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part016 : ℚ :=
  (15494231061 : ℚ) / 391324324436377600

def SurrogateDiagonalTailChunk001Sub001Block101Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28905
    = surrogateDiagTailX0RatChunk001Sub001Block101Part016

theorem surrogateDiagonalTailChunk001Sub001Block101Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part016] using hcert

def TailChunk001Sub001Block101Part017SupportExplicit : Finset ℕ :=
  ([28906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part017 : ℚ :=
  (25498091675 : ℚ) / 33965451961083887616

def SurrogateDiagonalTailChunk001Sub001Block101Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28906
    = surrogateDiagTailX0RatChunk001Sub001Block101Part017

theorem surrogateDiagonalTailChunk001Sub001Block101Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part017] using hcert

def TailChunk001Sub001Block101Part018SupportExplicit : Finset ℕ :=
  ([28907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part018 : ℚ :=
  (128145151 : ℚ) / 1957224960062668800

def SurrogateDiagonalTailChunk001Sub001Block101Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28907
    = surrogateDiagTailX0RatChunk001Sub001Block101Part018

theorem surrogateDiagonalTailChunk001Sub001Block101Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part018] using hcert

def TailChunk001Sub001Block101Part019SupportExplicit : Finset ℕ :=
  ([28909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block101Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28909
    = surrogateDiagTailX0RatChunk001Sub001Block101Part019

theorem surrogateDiagonalTailChunk001Sub001Block101Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part019] using hcert

def TailChunk001Sub001Block101Part020SupportExplicit : Finset ℕ :=
  ([28911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part020 : ℚ :=
  (5550186058825 : ℚ) / 286116360433122920448

def SurrogateDiagonalTailChunk001Sub001Block101Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28911
    = surrogateDiagTailX0RatChunk001Sub001Block101Part020

theorem surrogateDiagonalTailChunk001Sub001Block101Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part020] using hcert

def TailChunk001Sub001Block101Part021SupportExplicit : Finset ℕ :=
  ([28913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part021 : ℚ :=
  (79622309275 : ℚ) / 378125831157607636992

def SurrogateDiagonalTailChunk001Sub001Block101Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28913
    = surrogateDiagTailX0RatChunk001Sub001Block101Part021

theorem surrogateDiagonalTailChunk001Sub001Block101Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part021] using hcert

def TailChunk001Sub001Block101Part022SupportExplicit : Finset ℕ :=
  ([28914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part022 : ℚ :=
  (258399305 : ℚ) / 3411989822472192

def SurrogateDiagonalTailChunk001Sub001Block101Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28914
    = surrogateDiagTailX0RatChunk001Sub001Block101Part022

theorem surrogateDiagonalTailChunk001Sub001Block101Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part022] using hcert

def TailChunk001Sub001Block101Part023SupportExplicit : Finset ℕ :=
  ([28915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part023 : ℚ :=
  (696906904875 : ℚ) / 238483270468686616576

def SurrogateDiagonalTailChunk001Sub001Block101Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28915
    = surrogateDiagTailX0RatChunk001Sub001Block101Part023

theorem surrogateDiagonalTailChunk001Sub001Block101Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part023] using hcert

def TailChunk001Sub001Block101Part024SupportExplicit : Finset ℕ :=
  ([28918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block101Part024 : ℚ :=
  (177604637 : ℚ) / 70058564666671104

def SurrogateDiagonalTailChunk001Sub001Block101Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28918
    = surrogateDiagTailX0RatChunk001Sub001Block101Part024

theorem surrogateDiagonalTailChunk001Sub001Block101Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block101Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block101Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block101Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block101Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block101Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block101Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block101HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block101Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block101Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block101Part000
    + surrogateDiagTailX0RatChunk001Sub001Block101Part001
    + surrogateDiagTailX0RatChunk001Sub001Block101Part002
    + surrogateDiagTailX0RatChunk001Sub001Block101Part003
    + surrogateDiagTailX0RatChunk001Sub001Block101Part004
    + surrogateDiagTailX0RatChunk001Sub001Block101Part005
    + surrogateDiagTailX0RatChunk001Sub001Block101Part006
    + surrogateDiagTailX0RatChunk001Sub001Block101Part007
    + surrogateDiagTailX0RatChunk001Sub001Block101Part008
    + surrogateDiagTailX0RatChunk001Sub001Block101Part009

def surrogateDiagonalTailChunk001Sub001Block101MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block101Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block101Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block101Part010
    + surrogateDiagTailX0RatChunk001Sub001Block101Part011
    + surrogateDiagTailX0RatChunk001Sub001Block101Part012
    + surrogateDiagTailX0RatChunk001Sub001Block101Part013
    + surrogateDiagTailX0RatChunk001Sub001Block101Part014
    + surrogateDiagTailX0RatChunk001Sub001Block101Part015
    + surrogateDiagTailX0RatChunk001Sub001Block101Part016
    + surrogateDiagTailX0RatChunk001Sub001Block101Part017
    + surrogateDiagTailX0RatChunk001Sub001Block101Part018
    + surrogateDiagTailX0RatChunk001Sub001Block101Part019

def surrogateDiagonalTailChunk001Sub001Block101TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block101Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block101Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block101Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block101Part020
    + surrogateDiagTailX0RatChunk001Sub001Block101Part021
    + surrogateDiagTailX0RatChunk001Sub001Block101Part022
    + surrogateDiagTailX0RatChunk001Sub001Block101Part023
    + surrogateDiagTailX0RatChunk001Sub001Block101Part024

def surrogateDiagonalTailChunk001Sub001Block101Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block101HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block101MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block101TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block101 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block101Part000
    + surrogateDiagTailX0RatChunk001Sub001Block101Part001
    + surrogateDiagTailX0RatChunk001Sub001Block101Part002
    + surrogateDiagTailX0RatChunk001Sub001Block101Part003
    + surrogateDiagTailX0RatChunk001Sub001Block101Part004
    + surrogateDiagTailX0RatChunk001Sub001Block101Part005
    + surrogateDiagTailX0RatChunk001Sub001Block101Part006
    + surrogateDiagTailX0RatChunk001Sub001Block101Part007
    + surrogateDiagTailX0RatChunk001Sub001Block101Part008
    + surrogateDiagTailX0RatChunk001Sub001Block101Part009
    + surrogateDiagTailX0RatChunk001Sub001Block101Part010
    + surrogateDiagTailX0RatChunk001Sub001Block101Part011
    + surrogateDiagTailX0RatChunk001Sub001Block101Part012
    + surrogateDiagTailX0RatChunk001Sub001Block101Part013
    + surrogateDiagTailX0RatChunk001Sub001Block101Part014
    + surrogateDiagTailX0RatChunk001Sub001Block101Part015
    + surrogateDiagTailX0RatChunk001Sub001Block101Part016
    + surrogateDiagTailX0RatChunk001Sub001Block101Part017
    + surrogateDiagTailX0RatChunk001Sub001Block101Part018
    + surrogateDiagTailX0RatChunk001Sub001Block101Part019
    + surrogateDiagTailX0RatChunk001Sub001Block101Part020
    + surrogateDiagTailX0RatChunk001Sub001Block101Part021
    + surrogateDiagTailX0RatChunk001Sub001Block101Part022
    + surrogateDiagTailX0RatChunk001Sub001Block101Part023
    + surrogateDiagTailX0RatChunk001Sub001Block101Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block101_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block101Head + surrogateDiagTailX0RatChunk001Sub001Block101Mid + surrogateDiagTailX0RatChunk001Sub001Block101Tail =
      surrogateDiagTailX0RatChunk001Sub001Block101 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block101Head surrogateDiagTailX0RatChunk001Sub001Block101Mid surrogateDiagTailX0RatChunk001Sub001Block101Tail surrogateDiagTailX0RatChunk001Sub001Block101
  ring

def SurrogateDiagonalTailChunk001Sub001Block101HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block101HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block101Head

def SurrogateDiagonalTailChunk001Sub001Block101MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block101MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block101Mid

def SurrogateDiagonalTailChunk001Sub001Block101TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block101TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block101Tail

theorem surrogateDiagonalTailChunk001Sub001Block101_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block101HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block101MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block101TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block101Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block101 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block101HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block101MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block101TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block101Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block101_eq_head_add_mid_add_tail

/-- Block 102 covers tail-support indices [17550,17575) and q from 28921 to 28961. -/

def TailChunk001Sub001Block102Part000SupportExplicit : Finset ℕ :=
  ([28921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block102Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28921
    = surrogateDiagTailX0RatChunk001Sub001Block102Part000

theorem surrogateDiagonalTailChunk001Sub001Block102Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part000] using hcert

def TailChunk001Sub001Block102Part001SupportExplicit : Finset ℕ :=
  ([28922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block102Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28922
    = surrogateDiagTailX0RatChunk001Sub001Block102Part001

theorem surrogateDiagonalTailChunk001Sub001Block102Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part001] using hcert

def TailChunk001Sub001Block102Part002SupportExplicit : Finset ℕ :=
  ([28923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part002 : ℚ :=
  (44978772431 : ℚ) / 2394245185286400000

def SurrogateDiagonalTailChunk001Sub001Block102Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28923
    = surrogateDiagTailX0RatChunk001Sub001Block102Part002

theorem surrogateDiagonalTailChunk001Sub001Block102Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part002] using hcert

def TailChunk001Sub001Block102Part003SupportExplicit : Finset ℕ :=
  ([28927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block102Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28927
    = surrogateDiagTailX0RatChunk001Sub001Block102Part003

theorem surrogateDiagonalTailChunk001Sub001Block102Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part003] using hcert

def TailChunk001Sub001Block102Part004SupportExplicit : Finset ℕ :=
  ([28929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part004 : ℚ :=
  (2905567598225 : ℚ) / 172896162668688043584

def SurrogateDiagonalTailChunk001Sub001Block102Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28929
    = surrogateDiagTailX0RatChunk001Sub001Block102Part004

theorem surrogateDiagonalTailChunk001Sub001Block102Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part004] using hcert

def TailChunk001Sub001Block102Part005SupportExplicit : Finset ℕ :=
  ([28930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part005 : ℚ :=
  (16009034547 : ℚ) / 402170976917094400

def SurrogateDiagonalTailChunk001Sub001Block102Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28930
    = surrogateDiagTailX0RatChunk001Sub001Block102Part005

theorem surrogateDiagonalTailChunk001Sub001Block102Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part005] using hcert

def TailChunk001Sub001Block102Part006SupportExplicit : Finset ℕ :=
  ([28931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part006 : ℚ :=
  (1067813029175 : ℚ) / 472327374061212263424

def SurrogateDiagonalTailChunk001Sub001Block102Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28931
    = surrogateDiagTailX0RatChunk001Sub001Block102Part006

theorem surrogateDiagonalTailChunk001Sub001Block102Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part006] using hcert

def TailChunk001Sub001Block102Part007SupportExplicit : Finset ℕ :=
  ([28933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block102Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28933
    = surrogateDiagTailX0RatChunk001Sub001Block102Part007

theorem surrogateDiagonalTailChunk001Sub001Block102Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part007] using hcert

def TailChunk001Sub001Block102Part008SupportExplicit : Finset ℕ :=
  ([28934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part008 : ℚ :=
  (57997540025 : ℚ) / 7164155543936827392

def SurrogateDiagonalTailChunk001Sub001Block102Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28934
    = surrogateDiagTailX0RatChunk001Sub001Block102Part008

theorem surrogateDiagonalTailChunk001Sub001Block102Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part008] using hcert

def TailChunk001Sub001Block102Part009SupportExplicit : Finset ℕ :=
  ([28937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part009 : ℚ :=
  (439789939675 : ℚ) / 1408560446963105612928

def SurrogateDiagonalTailChunk001Sub001Block102Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28937
    = surrogateDiagTailX0RatChunk001Sub001Block102Part009

theorem surrogateDiagonalTailChunk001Sub001Block102Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part009] using hcert

def TailChunk001Sub001Block102Part010SupportExplicit : Finset ℕ :=
  ([28938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part010 : ℚ :=
  (81262081175 : ℚ) / 436734697276440576

def SurrogateDiagonalTailChunk001Sub001Block102Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28938
    = surrogateDiagTailX0RatChunk001Sub001Block102Part010

theorem surrogateDiagonalTailChunk001Sub001Block102Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part010] using hcert

def TailChunk001Sub001Block102Part011SupportExplicit : Finset ℕ :=
  ([28939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part011 : ℚ :=
  (119338703375 : ℚ) / 793361492116707999744

def SurrogateDiagonalTailChunk001Sub001Block102Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28939
    = surrogateDiagTailX0RatChunk001Sub001Block102Part011

theorem surrogateDiagonalTailChunk001Sub001Block102Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part011] using hcert

def TailChunk001Sub001Block102Part012SupportExplicit : Finset ℕ :=
  ([28941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part012 : ℚ :=
  (4110663161 : ℚ) / 188474783539544064

def SurrogateDiagonalTailChunk001Sub001Block102Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28941
    = surrogateDiagTailX0RatChunk001Sub001Block102Part012

theorem surrogateDiagonalTailChunk001Sub001Block102Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part012] using hcert

def TailChunk001Sub001Block102Part013SupportExplicit : Finset ℕ :=
  ([28942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part013 : ℚ :=
  (54484934075 : ℚ) / 31510485929800636416

def SurrogateDiagonalTailChunk001Sub001Block102Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28942
    = surrogateDiagTailX0RatChunk001Sub001Block102Part013

theorem surrogateDiagonalTailChunk001Sub001Block102Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part013] using hcert

def TailChunk001Sub001Block102Part014SupportExplicit : Finset ℕ :=
  ([28943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part014 : ℚ :=
  (318421 : ℚ) / 4435489478246400

def SurrogateDiagonalTailChunk001Sub001Block102Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28943
    = surrogateDiagTailX0RatChunk001Sub001Block102Part014

theorem surrogateDiagonalTailChunk001Sub001Block102Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part014] using hcert

def TailChunk001Sub001Block102Part015SupportExplicit : Finset ℕ :=
  ([28945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part015 : ℚ :=
  (3034672270075 : ℚ) / 386181988997190156288

def SurrogateDiagonalTailChunk001Sub001Block102Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28945
    = surrogateDiagTailX0RatChunk001Sub001Block102Part015

theorem surrogateDiagonalTailChunk001Sub001Block102Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part015] using hcert

def TailChunk001Sub001Block102Part016SupportExplicit : Finset ℕ :=
  ([28946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part016 : ℚ :=
  (1206388309 : ℚ) / 982737385999564800

def SurrogateDiagonalTailChunk001Sub001Block102Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28946
    = surrogateDiagTailX0RatChunk001Sub001Block102Part016

theorem surrogateDiagonalTailChunk001Sub001Block102Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part016] using hcert

def TailChunk001Sub001Block102Part017SupportExplicit : Finset ℕ :=
  ([28947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part017 : ℚ :=
  (1454592236575 : ℚ) / 86663461065179922432

def SurrogateDiagonalTailChunk001Sub001Block102Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28947
    = surrogateDiagTailX0RatChunk001Sub001Block102Part017

theorem surrogateDiagonalTailChunk001Sub001Block102Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part017] using hcert

def TailChunk001Sub001Block102Part018SupportExplicit : Finset ℕ :=
  ([28949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block102Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28949
    = surrogateDiagTailX0RatChunk001Sub001Block102Part018

theorem surrogateDiagonalTailChunk001Sub001Block102Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part018] using hcert

def TailChunk001Sub001Block102Part019SupportExplicit : Finset ℕ :=
  ([28951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part019 : ℚ :=
  (10926991561 : ℚ) / 9705215495032012800

def SurrogateDiagonalTailChunk001Sub001Block102Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28951
    = surrogateDiagTailX0RatChunk001Sub001Block102Part019

theorem surrogateDiagonalTailChunk001Sub001Block102Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part019] using hcert

def TailChunk001Sub001Block102Part020SupportExplicit : Finset ℕ :=
  ([28954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part020 : ℚ :=
  (1055706443 : ℚ) / 636743155702507200

def SurrogateDiagonalTailChunk001Sub001Block102Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28954
    = surrogateDiagTailX0RatChunk001Sub001Block102Part020

theorem surrogateDiagonalTailChunk001Sub001Block102Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part020] using hcert

def TailChunk001Sub001Block102Part021SupportExplicit : Finset ℕ :=
  ([28955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part021 : ℚ :=
  (16772053709 : ℚ) / 5755341075794749440

def SurrogateDiagonalTailChunk001Sub001Block102Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28955
    = surrogateDiagTailX0RatChunk001Sub001Block102Part021

theorem surrogateDiagonalTailChunk001Sub001Block102Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part021] using hcert

def TailChunk001Sub001Block102Part022SupportExplicit : Finset ℕ :=
  ([28957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part022 : ℚ :=
  (201134371175 : ℚ) / 733516944997779438144

def SurrogateDiagonalTailChunk001Sub001Block102Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28957
    = surrogateDiagTailX0RatChunk001Sub001Block102Part022

theorem surrogateDiagonalTailChunk001Sub001Block102Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part022] using hcert

def TailChunk001Sub001Block102Part023SupportExplicit : Finset ℕ :=
  ([28958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block102Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28958
    = surrogateDiagTailX0RatChunk001Sub001Block102Part023

theorem surrogateDiagonalTailChunk001Sub001Block102Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part023] using hcert

def TailChunk001Sub001Block102Part024SupportExplicit : Finset ℕ :=
  ([28961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block102Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block102Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28961
    = surrogateDiagTailX0RatChunk001Sub001Block102Part024

theorem surrogateDiagonalTailChunk001Sub001Block102Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block102Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block102Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block102Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block102Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block102Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block102Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block102HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block102Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block102Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block102Part000
    + surrogateDiagTailX0RatChunk001Sub001Block102Part001
    + surrogateDiagTailX0RatChunk001Sub001Block102Part002
    + surrogateDiagTailX0RatChunk001Sub001Block102Part003
    + surrogateDiagTailX0RatChunk001Sub001Block102Part004
    + surrogateDiagTailX0RatChunk001Sub001Block102Part005
    + surrogateDiagTailX0RatChunk001Sub001Block102Part006
    + surrogateDiagTailX0RatChunk001Sub001Block102Part007
    + surrogateDiagTailX0RatChunk001Sub001Block102Part008
    + surrogateDiagTailX0RatChunk001Sub001Block102Part009

def surrogateDiagonalTailChunk001Sub001Block102MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block102Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block102Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block102Part010
    + surrogateDiagTailX0RatChunk001Sub001Block102Part011
    + surrogateDiagTailX0RatChunk001Sub001Block102Part012
    + surrogateDiagTailX0RatChunk001Sub001Block102Part013
    + surrogateDiagTailX0RatChunk001Sub001Block102Part014
    + surrogateDiagTailX0RatChunk001Sub001Block102Part015
    + surrogateDiagTailX0RatChunk001Sub001Block102Part016
    + surrogateDiagTailX0RatChunk001Sub001Block102Part017
    + surrogateDiagTailX0RatChunk001Sub001Block102Part018
    + surrogateDiagTailX0RatChunk001Sub001Block102Part019

def surrogateDiagonalTailChunk001Sub001Block102TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block102Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block102Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block102Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block102Part020
    + surrogateDiagTailX0RatChunk001Sub001Block102Part021
    + surrogateDiagTailX0RatChunk001Sub001Block102Part022
    + surrogateDiagTailX0RatChunk001Sub001Block102Part023
    + surrogateDiagTailX0RatChunk001Sub001Block102Part024

def surrogateDiagonalTailChunk001Sub001Block102Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block102HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block102MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block102TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block102 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block102Part000
    + surrogateDiagTailX0RatChunk001Sub001Block102Part001
    + surrogateDiagTailX0RatChunk001Sub001Block102Part002
    + surrogateDiagTailX0RatChunk001Sub001Block102Part003
    + surrogateDiagTailX0RatChunk001Sub001Block102Part004
    + surrogateDiagTailX0RatChunk001Sub001Block102Part005
    + surrogateDiagTailX0RatChunk001Sub001Block102Part006
    + surrogateDiagTailX0RatChunk001Sub001Block102Part007
    + surrogateDiagTailX0RatChunk001Sub001Block102Part008
    + surrogateDiagTailX0RatChunk001Sub001Block102Part009
    + surrogateDiagTailX0RatChunk001Sub001Block102Part010
    + surrogateDiagTailX0RatChunk001Sub001Block102Part011
    + surrogateDiagTailX0RatChunk001Sub001Block102Part012
    + surrogateDiagTailX0RatChunk001Sub001Block102Part013
    + surrogateDiagTailX0RatChunk001Sub001Block102Part014
    + surrogateDiagTailX0RatChunk001Sub001Block102Part015
    + surrogateDiagTailX0RatChunk001Sub001Block102Part016
    + surrogateDiagTailX0RatChunk001Sub001Block102Part017
    + surrogateDiagTailX0RatChunk001Sub001Block102Part018
    + surrogateDiagTailX0RatChunk001Sub001Block102Part019
    + surrogateDiagTailX0RatChunk001Sub001Block102Part020
    + surrogateDiagTailX0RatChunk001Sub001Block102Part021
    + surrogateDiagTailX0RatChunk001Sub001Block102Part022
    + surrogateDiagTailX0RatChunk001Sub001Block102Part023
    + surrogateDiagTailX0RatChunk001Sub001Block102Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block102_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block102Head + surrogateDiagTailX0RatChunk001Sub001Block102Mid + surrogateDiagTailX0RatChunk001Sub001Block102Tail =
      surrogateDiagTailX0RatChunk001Sub001Block102 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block102Head surrogateDiagTailX0RatChunk001Sub001Block102Mid surrogateDiagTailX0RatChunk001Sub001Block102Tail surrogateDiagTailX0RatChunk001Sub001Block102
  ring

def SurrogateDiagonalTailChunk001Sub001Block102HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block102HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block102Head

def SurrogateDiagonalTailChunk001Sub001Block102MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block102MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block102Mid

def SurrogateDiagonalTailChunk001Sub001Block102TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block102TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block102Tail

theorem surrogateDiagonalTailChunk001Sub001Block102_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block102HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block102MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block102TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block102Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block102 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block102HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block102MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block102TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block102Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block102_eq_head_add_mid_add_tail

/-- Block 103 covers tail-support indices [17575,17600) and q from 28963 to 29001. -/

def TailChunk001Sub001Block103Part000SupportExplicit : Finset ℕ :=
  ([28963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part000 : ℚ :=
  (8688823999 : ℚ) / 11999700279107788800

def SurrogateDiagonalTailChunk001Sub001Block103Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28963
    = surrogateDiagTailX0RatChunk001Sub001Block103Part000

theorem surrogateDiagonalTailChunk001Sub001Block103Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part000] using hcert

def TailChunk001Sub001Block103Part001SupportExplicit : Finset ℕ :=
  ([28965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part001 : ℚ :=
  (254752371 : ℚ) / 7401415992534400

def SurrogateDiagonalTailChunk001Sub001Block103Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28965
    = surrogateDiagTailX0RatChunk001Sub001Block103Part001

theorem surrogateDiagonalTailChunk001Sub001Block103Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part001] using hcert

def TailChunk001Sub001Block103Part002SupportExplicit : Finset ℕ :=
  ([28966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part002 : ℚ :=
  (44634493225 : ℚ) / 3292770733189825536

def SurrogateDiagonalTailChunk001Sub001Block103Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28966
    = surrogateDiagTailX0RatChunk001Sub001Block103Part002

theorem surrogateDiagonalTailChunk001Sub001Block103Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part002] using hcert

def TailChunk001Sub001Block103Part003SupportExplicit : Finset ℕ :=
  ([28967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part003 : ℚ :=
  (131219382475 : ℚ) / 1658056189620097271808

def SurrogateDiagonalTailChunk001Sub001Block103Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28967
    = surrogateDiagTailX0RatChunk001Sub001Block103Part003

theorem surrogateDiagonalTailChunk001Sub001Block103Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part003] using hcert

def TailChunk001Sub001Block103Part004SupportExplicit : Finset ℕ :=
  ([28969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part004 : ℚ :=
  (191966801 : ℚ) / 1864296997908213120

def SurrogateDiagonalTailChunk001Sub001Block103Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28969
    = surrogateDiagTailX0RatChunk001Sub001Block103Part004

theorem surrogateDiagonalTailChunk001Sub001Block103Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part004] using hcert

def TailChunk001Sub001Block103Part005SupportExplicit : Finset ℕ :=
  ([28970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part005 : ℚ :=
  (1049392585525 : ℚ) / 45025760226802925568

def SurrogateDiagonalTailChunk001Sub001Block103Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28970
    = surrogateDiagTailX0RatChunk001Sub001Block103Part005

theorem surrogateDiagonalTailChunk001Sub001Block103Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part005] using hcert

def TailChunk001Sub001Block103Part006SupportExplicit : Finset ℕ :=
  ([28973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part006 : ℚ :=
  (1070913659075 : ℚ) / 475076786396023923264

def SurrogateDiagonalTailChunk001Sub001Block103Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28973
    = surrogateDiagTailX0RatChunk001Sub001Block103Part006

theorem surrogateDiagonalTailChunk001Sub001Block103Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part006] using hcert

def TailChunk001Sub001Block103Part007SupportExplicit : Finset ℕ :=
  ([28974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part007 : ℚ :=
  (1481058391 : ℚ) / 14724592464026880

def SurrogateDiagonalTailChunk001Sub001Block103Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28974
    = surrogateDiagTailX0RatChunk001Sub001Block103Part007

theorem surrogateDiagonalTailChunk001Sub001Block103Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part007] using hcert

def TailChunk001Sub001Block103Part008SupportExplicit : Finset ℕ :=
  ([28977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part008 : ℚ :=
  (2687785808675 : ℚ) / 125735366253614874624

def SurrogateDiagonalTailChunk001Sub001Block103Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28977
    = surrogateDiagTailX0RatChunk001Sub001Block103Part008

theorem surrogateDiagonalTailChunk001Sub001Block103Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part008] using hcert

def TailChunk001Sub001Block103Part009SupportExplicit : Finset ℕ :=
  ([28978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block103Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28978
    = surrogateDiagTailX0RatChunk001Sub001Block103Part009

theorem surrogateDiagonalTailChunk001Sub001Block103Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part009] using hcert

def TailChunk001Sub001Block103Part010SupportExplicit : Finset ℕ :=
  ([28979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block103Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28979
    = surrogateDiagTailX0RatChunk001Sub001Block103Part010

theorem surrogateDiagonalTailChunk001Sub001Block103Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part010] using hcert

def TailChunk001Sub001Block103Part011SupportExplicit : Finset ℕ :=
  ([28981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part011 : ℚ :=
  (51253175 : ℚ) / 566695897518440448

def SurrogateDiagonalTailChunk001Sub001Block103Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28981
    = surrogateDiagTailX0RatChunk001Sub001Block103Part011

theorem surrogateDiagonalTailChunk001Sub001Block103Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part011] using hcert

def TailChunk001Sub001Block103Part012SupportExplicit : Finset ℕ :=
  ([28982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part012 : ℚ :=
  (1099482925 : ℚ) / 918242467727671296

def SurrogateDiagonalTailChunk001Sub001Block103Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28982
    = surrogateDiagTailX0RatChunk001Sub001Block103Part012

theorem surrogateDiagonalTailChunk001Sub001Block103Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part012] using hcert

def TailChunk001Sub001Block103Part013SupportExplicit : Finset ℕ :=
  ([28983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part013 : ℚ :=
  (59518877 : ℚ) / 3554915413714560

def SurrogateDiagonalTailChunk001Sub001Block103Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28983
    = surrogateDiagTailX0RatChunk001Sub001Block103Part013

theorem surrogateDiagonalTailChunk001Sub001Block103Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part013] using hcert

def TailChunk001Sub001Block103Part014SupportExplicit : Finset ℕ :=
  ([28985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part014 : ℚ :=
  (5144998013 : ℚ) / 679613143449600000

def SurrogateDiagonalTailChunk001Sub001Block103Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28985
    = surrogateDiagTailX0RatChunk001Sub001Block103Part014

theorem surrogateDiagonalTailChunk001Sub001Block103Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part014] using hcert

def TailChunk001Sub001Block103Part015SupportExplicit : Finset ℕ :=
  ([28986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part015 : ℚ :=
  (833532181 : ℚ) / 12442203948000960

def SurrogateDiagonalTailChunk001Sub001Block103Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28986
    = surrogateDiagTailX0RatChunk001Sub001Block103Part015

theorem surrogateDiagonalTailChunk001Sub001Block103Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part015] using hcert

def TailChunk001Sub001Block103Part016SupportExplicit : Finset ℕ :=
  ([28987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part016 : ℚ :=
  (5028882409 : ℚ) / 3318423552000000000

def SurrogateDiagonalTailChunk001Sub001Block103Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28987
    = surrogateDiagTailX0RatChunk001Sub001Block103Part016

theorem surrogateDiagonalTailChunk001Sub001Block103Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part016] using hcert

def TailChunk001Sub001Block103Part017SupportExplicit : Finset ℕ :=
  ([28990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part017 : ℚ :=
  (574197970475 : ℚ) / 16120321926842548224

def SurrogateDiagonalTailChunk001Sub001Block103Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28990
    = surrogateDiagTailX0RatChunk001Sub001Block103Part017

theorem surrogateDiagonalTailChunk001Sub001Block103Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part017] using hcert

def TailChunk001Sub001Block103Part018SupportExplicit : Finset ℕ :=
  ([28991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part018 : ℚ :=
  (1009785575 : ℚ) / 8927696467049278464

def SurrogateDiagonalTailChunk001Sub001Block103Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28991
    = surrogateDiagTailX0RatChunk001Sub001Block103Part018

theorem surrogateDiagonalTailChunk001Sub001Block103Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part018] using hcert

def TailChunk001Sub001Block103Part019SupportExplicit : Finset ℕ :=
  ([28993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part019 : ℚ :=
  (70588191275 : ℚ) / 830423471054909719104

def SurrogateDiagonalTailChunk001Sub001Block103Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28993
    = surrogateDiagTailX0RatChunk001Sub001Block103Part019

theorem surrogateDiagonalTailChunk001Sub001Block103Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part019] using hcert

def TailChunk001Sub001Block103Part020SupportExplicit : Finset ℕ :=
  ([28994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part020 : ℚ :=
  (76755707725 : ℚ) / 5142501100899827712

def SurrogateDiagonalTailChunk001Sub001Block103Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28994
    = surrogateDiagTailX0RatChunk001Sub001Block103Part020

theorem surrogateDiagonalTailChunk001Sub001Block103Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part020] using hcert

def TailChunk001Sub001Block103Part021SupportExplicit : Finset ℕ :=
  ([28995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part021 : ℚ :=
  (2450691444125 : ℚ) / 71348574319416705024

def SurrogateDiagonalTailChunk001Sub001Block103Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28995
    = surrogateDiagTailX0RatChunk001Sub001Block103Part021

theorem surrogateDiagonalTailChunk001Sub001Block103Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part021] using hcert

def TailChunk001Sub001Block103Part022SupportExplicit : Finset ℕ :=
  ([28997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part022 : ℚ :=
  (1150489549 : ℚ) / 16776655112574496800

def SurrogateDiagonalTailChunk001Sub001Block103Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28997
    = surrogateDiagTailX0RatChunk001Sub001Block103Part022

theorem surrogateDiagonalTailChunk001Sub001Block103Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part022] using hcert

def TailChunk001Sub001Block103Part023SupportExplicit : Finset ℕ :=
  ([28999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part023 : ℚ :=
  (9704311275 : ℚ) / 76764732261212520448

def SurrogateDiagonalTailChunk001Sub001Block103Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28999
    = surrogateDiagTailX0RatChunk001Sub001Block103Part023

theorem surrogateDiagonalTailChunk001Sub001Block103Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part023] using hcert

def TailChunk001Sub001Block103Part024SupportExplicit : Finset ℕ :=
  ([29001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block103Part024 : ℚ :=
  (97671598613 : ℚ) / 3760955409121689600

def SurrogateDiagonalTailChunk001Sub001Block103Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29001
    = surrogateDiagTailX0RatChunk001Sub001Block103Part024

theorem surrogateDiagonalTailChunk001Sub001Block103Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block103Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block103Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block103Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block103Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block103Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block103Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block103HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block103Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block103Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block103Part000
    + surrogateDiagTailX0RatChunk001Sub001Block103Part001
    + surrogateDiagTailX0RatChunk001Sub001Block103Part002
    + surrogateDiagTailX0RatChunk001Sub001Block103Part003
    + surrogateDiagTailX0RatChunk001Sub001Block103Part004
    + surrogateDiagTailX0RatChunk001Sub001Block103Part005
    + surrogateDiagTailX0RatChunk001Sub001Block103Part006
    + surrogateDiagTailX0RatChunk001Sub001Block103Part007
    + surrogateDiagTailX0RatChunk001Sub001Block103Part008
    + surrogateDiagTailX0RatChunk001Sub001Block103Part009

def surrogateDiagonalTailChunk001Sub001Block103MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block103Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block103Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block103Part010
    + surrogateDiagTailX0RatChunk001Sub001Block103Part011
    + surrogateDiagTailX0RatChunk001Sub001Block103Part012
    + surrogateDiagTailX0RatChunk001Sub001Block103Part013
    + surrogateDiagTailX0RatChunk001Sub001Block103Part014
    + surrogateDiagTailX0RatChunk001Sub001Block103Part015
    + surrogateDiagTailX0RatChunk001Sub001Block103Part016
    + surrogateDiagTailX0RatChunk001Sub001Block103Part017
    + surrogateDiagTailX0RatChunk001Sub001Block103Part018
    + surrogateDiagTailX0RatChunk001Sub001Block103Part019

def surrogateDiagonalTailChunk001Sub001Block103TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block103Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block103Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block103Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block103Part020
    + surrogateDiagTailX0RatChunk001Sub001Block103Part021
    + surrogateDiagTailX0RatChunk001Sub001Block103Part022
    + surrogateDiagTailX0RatChunk001Sub001Block103Part023
    + surrogateDiagTailX0RatChunk001Sub001Block103Part024

def surrogateDiagonalTailChunk001Sub001Block103Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block103HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block103MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block103TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block103 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block103Part000
    + surrogateDiagTailX0RatChunk001Sub001Block103Part001
    + surrogateDiagTailX0RatChunk001Sub001Block103Part002
    + surrogateDiagTailX0RatChunk001Sub001Block103Part003
    + surrogateDiagTailX0RatChunk001Sub001Block103Part004
    + surrogateDiagTailX0RatChunk001Sub001Block103Part005
    + surrogateDiagTailX0RatChunk001Sub001Block103Part006
    + surrogateDiagTailX0RatChunk001Sub001Block103Part007
    + surrogateDiagTailX0RatChunk001Sub001Block103Part008
    + surrogateDiagTailX0RatChunk001Sub001Block103Part009
    + surrogateDiagTailX0RatChunk001Sub001Block103Part010
    + surrogateDiagTailX0RatChunk001Sub001Block103Part011
    + surrogateDiagTailX0RatChunk001Sub001Block103Part012
    + surrogateDiagTailX0RatChunk001Sub001Block103Part013
    + surrogateDiagTailX0RatChunk001Sub001Block103Part014
    + surrogateDiagTailX0RatChunk001Sub001Block103Part015
    + surrogateDiagTailX0RatChunk001Sub001Block103Part016
    + surrogateDiagTailX0RatChunk001Sub001Block103Part017
    + surrogateDiagTailX0RatChunk001Sub001Block103Part018
    + surrogateDiagTailX0RatChunk001Sub001Block103Part019
    + surrogateDiagTailX0RatChunk001Sub001Block103Part020
    + surrogateDiagTailX0RatChunk001Sub001Block103Part021
    + surrogateDiagTailX0RatChunk001Sub001Block103Part022
    + surrogateDiagTailX0RatChunk001Sub001Block103Part023
    + surrogateDiagTailX0RatChunk001Sub001Block103Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block103_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block103Head + surrogateDiagTailX0RatChunk001Sub001Block103Mid + surrogateDiagTailX0RatChunk001Sub001Block103Tail =
      surrogateDiagTailX0RatChunk001Sub001Block103 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block103Head surrogateDiagTailX0RatChunk001Sub001Block103Mid surrogateDiagTailX0RatChunk001Sub001Block103Tail surrogateDiagTailX0RatChunk001Sub001Block103
  ring

def SurrogateDiagonalTailChunk001Sub001Block103HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block103HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block103Head

def SurrogateDiagonalTailChunk001Sub001Block103MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block103MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block103Mid

def SurrogateDiagonalTailChunk001Sub001Block103TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block103TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block103Tail

theorem surrogateDiagonalTailChunk001Sub001Block103_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block103HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block103MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block103TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block103Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block103 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block103HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block103MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block103TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block103Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block103_eq_head_add_mid_add_tail

/-- Block 104 covers tail-support indices [17600,17625) and q from 29002 to 29038. -/

def TailChunk001Sub001Block104Part000SupportExplicit : Finset ℕ :=
  ([29002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part000 : ℚ :=
  (15385567475 : ℚ) / 4797253445763465216

def SurrogateDiagonalTailChunk001Sub001Block104Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29002
    = surrogateDiagTailX0RatChunk001Sub001Block104Part000

theorem surrogateDiagonalTailChunk001Sub001Block104Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part000] using hcert

def TailChunk001Sub001Block104Part001SupportExplicit : Finset ℕ :=
  ([29003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part001 : ℚ :=
  (165847824625 : ℚ) / 171939733054483857408

def SurrogateDiagonalTailChunk001Sub001Block104Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29003
    = surrogateDiagTailX0RatChunk001Sub001Block104Part001

theorem surrogateDiagonalTailChunk001Sub001Block104Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part001] using hcert

def TailChunk001Sub001Block104Part002SupportExplicit : Finset ℕ :=
  ([29005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part002 : ℚ :=
  (5610001233 : ℚ) / 1931734920396800000

def SurrogateDiagonalTailChunk001Sub001Block104Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29005
    = surrogateDiagTailX0RatChunk001Sub001Block104Part002

theorem surrogateDiagonalTailChunk001Sub001Block104Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part002] using hcert

def TailChunk001Sub001Block104Part003SupportExplicit : Finset ℕ :=
  ([29006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block104Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29006
    = surrogateDiagTailX0RatChunk001Sub001Block104Part003

theorem surrogateDiagonalTailChunk001Sub001Block104Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part003] using hcert

def TailChunk001Sub001Block104Part004SupportExplicit : Finset ℕ :=
  ([29009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block104Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29009
    = surrogateDiagTailX0RatChunk001Sub001Block104Part004

theorem surrogateDiagonalTailChunk001Sub001Block104Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part004] using hcert

def TailChunk001Sub001Block104Part005SupportExplicit : Finset ℕ :=
  ([29010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part005 : ℚ :=
  (189845179325 : ℚ) / 1114821473740886016

def SurrogateDiagonalTailChunk001Sub001Block104Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29010
    = surrogateDiagTailX0RatChunk001Sub001Block104Part005

theorem surrogateDiagonalTailChunk001Sub001Block104Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part005] using hcert

def TailChunk001Sub001Block104Part006SupportExplicit : Finset ℕ :=
  ([29011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part006 : ℚ :=
  (1980066775 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk001Sub001Block104Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29011
    = surrogateDiagTailX0RatChunk001Sub001Block104Part006

theorem surrogateDiagonalTailChunk001Sub001Block104Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part006] using hcert

def TailChunk001Sub001Block104Part007SupportExplicit : Finset ℕ :=
  ([29013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part007 : ℚ :=
  (1381853100025 : ℚ) / 69924878393299771392

def SurrogateDiagonalTailChunk001Sub001Block104Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29013
    = surrogateDiagTailX0RatChunk001Sub001Block104Part007

theorem surrogateDiagonalTailChunk001Sub001Block104Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part007] using hcert

def TailChunk001Sub001Block104Part008SupportExplicit : Finset ℕ :=
  ([29014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part008 : ℚ :=
  (39215120375 : ℚ) / 51640163661367885824

def SurrogateDiagonalTailChunk001Sub001Block104Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29014
    = surrogateDiagTailX0RatChunk001Sub001Block104Part008

theorem surrogateDiagonalTailChunk001Sub001Block104Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part008] using hcert

def TailChunk001Sub001Block104Part009SupportExplicit : Finset ℕ :=
  ([29015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part009 : ℚ :=
  (25075180625 : ℚ) / 4061831841851424768

def SurrogateDiagonalTailChunk001Sub001Block104Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29015
    = surrogateDiagTailX0RatChunk001Sub001Block104Part009

theorem surrogateDiagonalTailChunk001Sub001Block104Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part009] using hcert

def TailChunk001Sub001Block104Part010SupportExplicit : Finset ℕ :=
  ([29017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block104Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29017
    = surrogateDiagTailX0RatChunk001Sub001Block104Part010

theorem surrogateDiagonalTailChunk001Sub001Block104Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part010] using hcert

def TailChunk001Sub001Block104Part011SupportExplicit : Finset ℕ :=
  ([29018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part011 : ℚ :=
  (13148323447 : ℚ) / 3018203311334275200

def SurrogateDiagonalTailChunk001Sub001Block104Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29018
    = surrogateDiagTailX0RatChunk001Sub001Block104Part011

theorem surrogateDiagonalTailChunk001Sub001Block104Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part011] using hcert

def TailChunk001Sub001Block104Part012SupportExplicit : Finset ℕ :=
  ([29019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part012 : ℚ :=
  (2757342338075 : ℚ) / 136455209123938566144

def SurrogateDiagonalTailChunk001Sub001Block104Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29019
    = surrogateDiagTailX0RatChunk001Sub001Block104Part012

theorem surrogateDiagonalTailChunk001Sub001Block104Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part012] using hcert

def TailChunk001Sub001Block104Part013SupportExplicit : Finset ℕ :=
  ([29021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block104Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29021
    = surrogateDiagTailX0RatChunk001Sub001Block104Part013

theorem surrogateDiagonalTailChunk001Sub001Block104Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part013] using hcert

def TailChunk001Sub001Block104Part014SupportExplicit : Finset ℕ :=
  ([29022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part014 : ℚ :=
  (6364966301 : ℚ) / 52235491793356800

def SurrogateDiagonalTailChunk001Sub001Block104Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29022
    = surrogateDiagTailX0RatChunk001Sub001Block104Part014

theorem surrogateDiagonalTailChunk001Sub001Block104Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part014] using hcert

def TailChunk001Sub001Block104Part015SupportExplicit : Finset ℕ :=
  ([29023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block104Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29023
    = surrogateDiagTailX0RatChunk001Sub001Block104Part015

theorem surrogateDiagonalTailChunk001Sub001Block104Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part015] using hcert

def TailChunk001Sub001Block104Part016SupportExplicit : Finset ℕ :=
  ([29026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part016 : ℚ :=
  (410073089 : ℚ) / 184548183857120160

def SurrogateDiagonalTailChunk001Sub001Block104Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29026
    = surrogateDiagTailX0RatChunk001Sub001Block104Part016

theorem surrogateDiagonalTailChunk001Sub001Block104Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part016] using hcert

def TailChunk001Sub001Block104Part017SupportExplicit : Finset ℕ :=
  ([29027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block104Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29027
    = surrogateDiagTailX0RatChunk001Sub001Block104Part017

theorem surrogateDiagonalTailChunk001Sub001Block104Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part017] using hcert

def TailChunk001Sub001Block104Part018SupportExplicit : Finset ℕ :=
  ([29029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part018 : ℚ :=
  (10672792253 : ℚ) / 2065185058612838400

def SurrogateDiagonalTailChunk001Sub001Block104Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29029
    = surrogateDiagTailX0RatChunk001Sub001Block104Part018

theorem surrogateDiagonalTailChunk001Sub001Block104Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part018] using hcert

def TailChunk001Sub001Block104Part019SupportExplicit : Finset ℕ :=
  ([29030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part019 : ℚ :=
  (175867024875 : ℚ) / 15133354371328546816

def SurrogateDiagonalTailChunk001Sub001Block104Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29030
    = surrogateDiagTailX0RatChunk001Sub001Block104Part019

theorem surrogateDiagonalTailChunk001Sub001Block104Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part019] using hcert

def TailChunk001Sub001Block104Part020SupportExplicit : Finset ℕ :=
  ([29031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part020 : ℚ :=
  (11430050675 : ℚ) / 684952285798966884

def SurrogateDiagonalTailChunk001Sub001Block104Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29031
    = surrogateDiagTailX0RatChunk001Sub001Block104Part020

theorem surrogateDiagonalTailChunk001Sub001Block104Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part020] using hcert

def TailChunk001Sub001Block104Part021SupportExplicit : Finset ℕ :=
  ([29033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block104Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29033
    = surrogateDiagTailX0RatChunk001Sub001Block104Part021

theorem surrogateDiagonalTailChunk001Sub001Block104Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part021] using hcert

def TailChunk001Sub001Block104Part022SupportExplicit : Finset ℕ :=
  ([29035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part022 : ℚ :=
  (78203125 : ℚ) / 45462673086573859968

def SurrogateDiagonalTailChunk001Sub001Block104Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29035
    = surrogateDiagTailX0RatChunk001Sub001Block104Part022

theorem surrogateDiagonalTailChunk001Sub001Block104Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part022] using hcert

def TailChunk001Sub001Block104Part023SupportExplicit : Finset ℕ :=
  ([29037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part023 : ℚ :=
  (2927302597775 : ℚ) / 175492805551838927424

def SurrogateDiagonalTailChunk001Sub001Block104Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29037
    = surrogateDiagTailX0RatChunk001Sub001Block104Part023

theorem surrogateDiagonalTailChunk001Sub001Block104Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part023] using hcert

def TailChunk001Sub001Block104Part024SupportExplicit : Finset ℕ :=
  ([29038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block104Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block104Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29038
    = surrogateDiagTailX0RatChunk001Sub001Block104Part024

theorem surrogateDiagonalTailChunk001Sub001Block104Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block104Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block104Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block104Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block104Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block104Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block104Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block104HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block104Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block104Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block104Part000
    + surrogateDiagTailX0RatChunk001Sub001Block104Part001
    + surrogateDiagTailX0RatChunk001Sub001Block104Part002
    + surrogateDiagTailX0RatChunk001Sub001Block104Part003
    + surrogateDiagTailX0RatChunk001Sub001Block104Part004
    + surrogateDiagTailX0RatChunk001Sub001Block104Part005
    + surrogateDiagTailX0RatChunk001Sub001Block104Part006
    + surrogateDiagTailX0RatChunk001Sub001Block104Part007
    + surrogateDiagTailX0RatChunk001Sub001Block104Part008
    + surrogateDiagTailX0RatChunk001Sub001Block104Part009

def surrogateDiagonalTailChunk001Sub001Block104MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block104Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block104Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block104Part010
    + surrogateDiagTailX0RatChunk001Sub001Block104Part011
    + surrogateDiagTailX0RatChunk001Sub001Block104Part012
    + surrogateDiagTailX0RatChunk001Sub001Block104Part013
    + surrogateDiagTailX0RatChunk001Sub001Block104Part014
    + surrogateDiagTailX0RatChunk001Sub001Block104Part015
    + surrogateDiagTailX0RatChunk001Sub001Block104Part016
    + surrogateDiagTailX0RatChunk001Sub001Block104Part017
    + surrogateDiagTailX0RatChunk001Sub001Block104Part018
    + surrogateDiagTailX0RatChunk001Sub001Block104Part019

def surrogateDiagonalTailChunk001Sub001Block104TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block104Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block104Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block104Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block104Part020
    + surrogateDiagTailX0RatChunk001Sub001Block104Part021
    + surrogateDiagTailX0RatChunk001Sub001Block104Part022
    + surrogateDiagTailX0RatChunk001Sub001Block104Part023
    + surrogateDiagTailX0RatChunk001Sub001Block104Part024

def surrogateDiagonalTailChunk001Sub001Block104Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block104HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block104MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block104TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block104 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block104Part000
    + surrogateDiagTailX0RatChunk001Sub001Block104Part001
    + surrogateDiagTailX0RatChunk001Sub001Block104Part002
    + surrogateDiagTailX0RatChunk001Sub001Block104Part003
    + surrogateDiagTailX0RatChunk001Sub001Block104Part004
    + surrogateDiagTailX0RatChunk001Sub001Block104Part005
    + surrogateDiagTailX0RatChunk001Sub001Block104Part006
    + surrogateDiagTailX0RatChunk001Sub001Block104Part007
    + surrogateDiagTailX0RatChunk001Sub001Block104Part008
    + surrogateDiagTailX0RatChunk001Sub001Block104Part009
    + surrogateDiagTailX0RatChunk001Sub001Block104Part010
    + surrogateDiagTailX0RatChunk001Sub001Block104Part011
    + surrogateDiagTailX0RatChunk001Sub001Block104Part012
    + surrogateDiagTailX0RatChunk001Sub001Block104Part013
    + surrogateDiagTailX0RatChunk001Sub001Block104Part014
    + surrogateDiagTailX0RatChunk001Sub001Block104Part015
    + surrogateDiagTailX0RatChunk001Sub001Block104Part016
    + surrogateDiagTailX0RatChunk001Sub001Block104Part017
    + surrogateDiagTailX0RatChunk001Sub001Block104Part018
    + surrogateDiagTailX0RatChunk001Sub001Block104Part019
    + surrogateDiagTailX0RatChunk001Sub001Block104Part020
    + surrogateDiagTailX0RatChunk001Sub001Block104Part021
    + surrogateDiagTailX0RatChunk001Sub001Block104Part022
    + surrogateDiagTailX0RatChunk001Sub001Block104Part023
    + surrogateDiagTailX0RatChunk001Sub001Block104Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block104_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block104Head + surrogateDiagTailX0RatChunk001Sub001Block104Mid + surrogateDiagTailX0RatChunk001Sub001Block104Tail =
      surrogateDiagTailX0RatChunk001Sub001Block104 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block104Head surrogateDiagTailX0RatChunk001Sub001Block104Mid surrogateDiagTailX0RatChunk001Sub001Block104Tail surrogateDiagTailX0RatChunk001Sub001Block104
  ring

def SurrogateDiagonalTailChunk001Sub001Block104HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block104HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block104Head

def SurrogateDiagonalTailChunk001Sub001Block104MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block104MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block104Mid

def SurrogateDiagonalTailChunk001Sub001Block104TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block104TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block104Tail

theorem surrogateDiagonalTailChunk001Sub001Block104_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block104HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block104MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block104TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block104Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block104 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block104HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block104MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block104TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block104Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block104_eq_head_add_mid_add_tail

/-- Block 105 covers tail-support indices [17625,17650) and q from 29039 to 29081. -/

def TailChunk001Sub001Block105Part000SupportExplicit : Finset ℕ :=
  ([29039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part000 : ℚ :=
  (5852997679 : ℚ) / 66545648642130739200

def SurrogateDiagonalTailChunk001Sub001Block105Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29039
    = surrogateDiagTailX0RatChunk001Sub001Block105Part000

theorem surrogateDiagonalTailChunk001Sub001Block105Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part000] using hcert

def TailChunk001Sub001Block105Part001SupportExplicit : Finset ℕ :=
  ([29041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part001 : ℚ :=
  (7070428525 : ℚ) / 105618216150953361408

def SurrogateDiagonalTailChunk001Sub001Block105Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29041
    = surrogateDiagTailX0RatChunk001Sub001Block105Part001

theorem surrogateDiagonalTailChunk001Sub001Block105Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part001] using hcert

def TailChunk001Sub001Block105Part002SupportExplicit : Finset ℕ :=
  ([29042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part002 : ℚ :=
  (43627368625 : ℚ) / 8936472269177782272

def SurrogateDiagonalTailChunk001Sub001Block105Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29042
    = surrogateDiagTailX0RatChunk001Sub001Block105Part002

theorem surrogateDiagonalTailChunk001Sub001Block105Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part002] using hcert

def TailChunk001Sub001Block105Part003SupportExplicit : Finset ℕ :=
  ([29045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part003 : ℚ :=
  (253373626525 : ℚ) / 636759188629050359808

def SurrogateDiagonalTailChunk001Sub001Block105Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29045
    = surrogateDiagTailX0RatChunk001Sub001Block105Part003

theorem surrogateDiagonalTailChunk001Sub001Block105Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part003] using hcert

def TailChunk001Sub001Block105Part004SupportExplicit : Finset ℕ :=
  ([29046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part004 : ℚ :=
  (754160075 : ℚ) / 9974303863907072

def SurrogateDiagonalTailChunk001Sub001Block105Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29046
    = surrogateDiagTailX0RatChunk001Sub001Block105Part004

theorem surrogateDiagonalTailChunk001Sub001Block105Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part004] using hcert

def TailChunk001Sub001Block105Part005SupportExplicit : Finset ℕ :=
  ([29047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part005 : ℚ :=
  (2263374959 : ℚ) / 12436702902911139840

def SurrogateDiagonalTailChunk001Sub001Block105Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29047
    = surrogateDiagTailX0RatChunk001Sub001Block105Part005

theorem surrogateDiagonalTailChunk001Sub001Block105Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part005] using hcert

def TailChunk001Sub001Block105Part006SupportExplicit : Finset ℕ :=
  ([29049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part006 : ℚ :=
  (8301176071 : ℚ) / 432046959921561600

def SurrogateDiagonalTailChunk001Sub001Block105Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29049
    = surrogateDiagTailX0RatChunk001Sub001Block105Part006

theorem surrogateDiagonalTailChunk001Sub001Block105Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part006] using hcert

def TailChunk001Sub001Block105Part007SupportExplicit : Finset ℕ :=
  ([29051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part007 : ℚ :=
  (4886171557 : ℚ) / 3807967351735710720

def SurrogateDiagonalTailChunk001Sub001Block105Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29051
    = surrogateDiagTailX0RatChunk001Sub001Block105Part007

theorem surrogateDiagonalTailChunk001Sub001Block105Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part007] using hcert

def TailChunk001Sub001Block105Part008SupportExplicit : Finset ℕ :=
  ([29053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part008 : ℚ :=
  (58648725 : ℚ) / 148238477610582016

def SurrogateDiagonalTailChunk001Sub001Block105Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29053
    = surrogateDiagTailX0RatChunk001Sub001Block105Part008

theorem surrogateDiagonalTailChunk001Sub001Block105Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part008] using hcert

def TailChunk001Sub001Block105Part009SupportExplicit : Finset ℕ :=
  ([29054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part009 : ℚ :=
  (38249275 : ℚ) / 47419801341935616

def SurrogateDiagonalTailChunk001Sub001Block105Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29054
    = surrogateDiagTailX0RatChunk001Sub001Block105Part009

theorem surrogateDiagonalTailChunk001Sub001Block105Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part009] using hcert

def TailChunk001Sub001Block105Part010SupportExplicit : Finset ℕ :=
  ([29055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part010 : ℚ :=
  (1232025373475 : ℚ) / 33965451961083887616

def SurrogateDiagonalTailChunk001Sub001Block105Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29055
    = surrogateDiagTailX0RatChunk001Sub001Block105Part010

theorem surrogateDiagonalTailChunk001Sub001Block105Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part010] using hcert

def TailChunk001Sub001Block105Part011SupportExplicit : Finset ℕ :=
  ([29058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part011 : ℚ :=
  (91397974075 : ℚ) / 1167055034437060608

def SurrogateDiagonalTailChunk001Sub001Block105Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29058
    = surrogateDiagTailX0RatChunk001Sub001Block105Part011

theorem surrogateDiagonalTailChunk001Sub001Block105Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part011] using hcert

def TailChunk001Sub001Block105Part012SupportExplicit : Finset ℕ :=
  ([29059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block105Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29059
    = surrogateDiagTailX0RatChunk001Sub001Block105Part012

theorem surrogateDiagonalTailChunk001Sub001Block105Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part012] using hcert

def TailChunk001Sub001Block105Part013SupportExplicit : Finset ℕ :=
  ([29062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part013 : ℚ :=
  (17538633349 : ℚ) / 3036564951552000000

def SurrogateDiagonalTailChunk001Sub001Block105Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29062
    = surrogateDiagTailX0RatChunk001Sub001Block105Part013

theorem surrogateDiagonalTailChunk001Sub001Block105Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part013] using hcert

def TailChunk001Sub001Block105Part014SupportExplicit : Finset ℕ :=
  ([29063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block105Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29063
    = surrogateDiagTailX0RatChunk001Sub001Block105Part014

theorem surrogateDiagonalTailChunk001Sub001Block105Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part014] using hcert

def TailChunk001Sub001Block105Part015SupportExplicit : Finset ℕ :=
  ([29065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part015 : ℚ :=
  (78203125 : ℚ) / 45650891595462002688

def SurrogateDiagonalTailChunk001Sub001Block105Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29065
    = surrogateDiagTailX0RatChunk001Sub001Block105Part015

theorem surrogateDiagonalTailChunk001Sub001Block105Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part015] using hcert

def TailChunk001Sub001Block105Part016SupportExplicit : Finset ℕ :=
  ([29066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block105Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29066
    = surrogateDiagTailX0RatChunk001Sub001Block105Part016

theorem surrogateDiagonalTailChunk001Sub001Block105Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part016] using hcert

def TailChunk001Sub001Block105Part017SupportExplicit : Finset ℕ :=
  ([29067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part017 : ℚ :=
  (209525319475 : ℚ) / 12587089804198404096

def SurrogateDiagonalTailChunk001Sub001Block105Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29067
    = surrogateDiagTailX0RatChunk001Sub001Block105Part017

theorem surrogateDiagonalTailChunk001Sub001Block105Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part017] using hcert

def TailChunk001Sub001Block105Part018SupportExplicit : Finset ℕ :=
  ([29069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part018 : ℚ :=
  (2315458453 : ℚ) / 16084214452194508800

def SurrogateDiagonalTailChunk001Sub001Block105Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29069
    = surrogateDiagTailX0RatChunk001Sub001Block105Part018

theorem surrogateDiagonalTailChunk001Sub001Block105Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part018] using hcert

def TailChunk001Sub001Block105Part019SupportExplicit : Finset ℕ :=
  ([29071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part019 : ℚ :=
  (1079318957425 : ℚ) / 963077506767880224768

def SurrogateDiagonalTailChunk001Sub001Block105Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29071
    = surrogateDiagTailX0RatChunk001Sub001Block105Part019

theorem surrogateDiagonalTailChunk001Sub001Block105Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part019] using hcert

def TailChunk001Sub001Block105Part020SupportExplicit : Finset ℕ :=
  ([29073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part020 : ℚ :=
  (35857027473 : ℚ) / 1599507464192000000

def SurrogateDiagonalTailChunk001Sub001Block105Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29073
    = surrogateDiagTailX0RatChunk001Sub001Block105Part020

theorem surrogateDiagonalTailChunk001Sub001Block105Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part020] using hcert

def TailChunk001Sub001Block105Part021SupportExplicit : Finset ℕ :=
  ([29074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block105Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29074
    = surrogateDiagTailX0RatChunk001Sub001Block105Part021

theorem surrogateDiagonalTailChunk001Sub001Block105Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part021] using hcert

def TailChunk001Sub001Block105Part022SupportExplicit : Finset ℕ :=
  ([29077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block105Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29077
    = surrogateDiagTailX0RatChunk001Sub001Block105Part022

theorem surrogateDiagonalTailChunk001Sub001Block105Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part022] using hcert

def TailChunk001Sub001Block105Part023SupportExplicit : Finset ℕ :=
  ([29078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part023 : ℚ :=
  (36226685767 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk001Sub001Block105Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29078
    = surrogateDiagTailX0RatChunk001Sub001Block105Part023

theorem surrogateDiagonalTailChunk001Sub001Block105Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part023] using hcert

def TailChunk001Sub001Block105Part024SupportExplicit : Finset ℕ :=
  ([29081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block105Part024 : ℚ :=
  (628590462025 : ℚ) / 1296101579673083609088

def SurrogateDiagonalTailChunk001Sub001Block105Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29081
    = surrogateDiagTailX0RatChunk001Sub001Block105Part024

theorem surrogateDiagonalTailChunk001Sub001Block105Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block105Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block105Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block105Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block105Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block105Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block105Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block105HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block105Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block105Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block105Part000
    + surrogateDiagTailX0RatChunk001Sub001Block105Part001
    + surrogateDiagTailX0RatChunk001Sub001Block105Part002
    + surrogateDiagTailX0RatChunk001Sub001Block105Part003
    + surrogateDiagTailX0RatChunk001Sub001Block105Part004
    + surrogateDiagTailX0RatChunk001Sub001Block105Part005
    + surrogateDiagTailX0RatChunk001Sub001Block105Part006
    + surrogateDiagTailX0RatChunk001Sub001Block105Part007
    + surrogateDiagTailX0RatChunk001Sub001Block105Part008
    + surrogateDiagTailX0RatChunk001Sub001Block105Part009

def surrogateDiagonalTailChunk001Sub001Block105MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block105Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block105Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block105Part010
    + surrogateDiagTailX0RatChunk001Sub001Block105Part011
    + surrogateDiagTailX0RatChunk001Sub001Block105Part012
    + surrogateDiagTailX0RatChunk001Sub001Block105Part013
    + surrogateDiagTailX0RatChunk001Sub001Block105Part014
    + surrogateDiagTailX0RatChunk001Sub001Block105Part015
    + surrogateDiagTailX0RatChunk001Sub001Block105Part016
    + surrogateDiagTailX0RatChunk001Sub001Block105Part017
    + surrogateDiagTailX0RatChunk001Sub001Block105Part018
    + surrogateDiagTailX0RatChunk001Sub001Block105Part019

def surrogateDiagonalTailChunk001Sub001Block105TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block105Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block105Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block105Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block105Part020
    + surrogateDiagTailX0RatChunk001Sub001Block105Part021
    + surrogateDiagTailX0RatChunk001Sub001Block105Part022
    + surrogateDiagTailX0RatChunk001Sub001Block105Part023
    + surrogateDiagTailX0RatChunk001Sub001Block105Part024

def surrogateDiagonalTailChunk001Sub001Block105Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block105HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block105MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block105TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block105 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block105Part000
    + surrogateDiagTailX0RatChunk001Sub001Block105Part001
    + surrogateDiagTailX0RatChunk001Sub001Block105Part002
    + surrogateDiagTailX0RatChunk001Sub001Block105Part003
    + surrogateDiagTailX0RatChunk001Sub001Block105Part004
    + surrogateDiagTailX0RatChunk001Sub001Block105Part005
    + surrogateDiagTailX0RatChunk001Sub001Block105Part006
    + surrogateDiagTailX0RatChunk001Sub001Block105Part007
    + surrogateDiagTailX0RatChunk001Sub001Block105Part008
    + surrogateDiagTailX0RatChunk001Sub001Block105Part009
    + surrogateDiagTailX0RatChunk001Sub001Block105Part010
    + surrogateDiagTailX0RatChunk001Sub001Block105Part011
    + surrogateDiagTailX0RatChunk001Sub001Block105Part012
    + surrogateDiagTailX0RatChunk001Sub001Block105Part013
    + surrogateDiagTailX0RatChunk001Sub001Block105Part014
    + surrogateDiagTailX0RatChunk001Sub001Block105Part015
    + surrogateDiagTailX0RatChunk001Sub001Block105Part016
    + surrogateDiagTailX0RatChunk001Sub001Block105Part017
    + surrogateDiagTailX0RatChunk001Sub001Block105Part018
    + surrogateDiagTailX0RatChunk001Sub001Block105Part019
    + surrogateDiagTailX0RatChunk001Sub001Block105Part020
    + surrogateDiagTailX0RatChunk001Sub001Block105Part021
    + surrogateDiagTailX0RatChunk001Sub001Block105Part022
    + surrogateDiagTailX0RatChunk001Sub001Block105Part023
    + surrogateDiagTailX0RatChunk001Sub001Block105Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block105_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block105Head + surrogateDiagTailX0RatChunk001Sub001Block105Mid + surrogateDiagTailX0RatChunk001Sub001Block105Tail =
      surrogateDiagTailX0RatChunk001Sub001Block105 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block105Head surrogateDiagTailX0RatChunk001Sub001Block105Mid surrogateDiagTailX0RatChunk001Sub001Block105Tail surrogateDiagTailX0RatChunk001Sub001Block105
  ring

def SurrogateDiagonalTailChunk001Sub001Block105HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block105HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block105Head

def SurrogateDiagonalTailChunk001Sub001Block105MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block105MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block105Mid

def SurrogateDiagonalTailChunk001Sub001Block105TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block105TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block105Tail

theorem surrogateDiagonalTailChunk001Sub001Block105_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block105HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block105MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block105TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block105Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block105 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block105HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block105MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block105TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block105Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block105_eq_head_add_mid_add_tail

/-- Block 106 covers tail-support indices [17650,17675) and q from 29082 to 29119. -/

def TailChunk001Sub001Block106Part000SupportExplicit : Finset ℕ :=
  ([29082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part000 : ℚ :=
  (58737193579 : ℚ) / 767697710056243200

def SurrogateDiagonalTailChunk001Sub001Block106Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29082
    = surrogateDiagTailX0RatChunk001Sub001Block106Part000

theorem surrogateDiagonalTailChunk001Sub001Block106Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part000] using hcert

def TailChunk001Sub001Block106Part001SupportExplicit : Finset ℕ :=
  ([29083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part001 : ℚ :=
  (55097672825 : ℚ) / 851566232183678936064

def SurrogateDiagonalTailChunk001Sub001Block106Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29083
    = surrogateDiagTailX0RatChunk001Sub001Block106Part001

theorem surrogateDiagonalTailChunk001Sub001Block106Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part001] using hcert

def TailChunk001Sub001Block106Part002SupportExplicit : Finset ℕ :=
  ([29085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part002 : ℚ :=
  (2056922623325 : ℚ) / 38512183389406101504

def SurrogateDiagonalTailChunk001Sub001Block106Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29085
    = surrogateDiagTailX0RatChunk001Sub001Block106Part002

theorem surrogateDiagonalTailChunk001Sub001Block106Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part002] using hcert

def TailChunk001Sub001Block106Part003SupportExplicit : Finset ℕ :=
  ([29086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block106Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29086
    = surrogateDiagTailX0RatChunk001Sub001Block106Part003

theorem surrogateDiagonalTailChunk001Sub001Block106Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part003] using hcert

def TailChunk001Sub001Block106Part004SupportExplicit : Finset ℕ :=
  ([29087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part004 : ℚ :=
  (458826366125 : ℚ) / 569929180431079440384

def SurrogateDiagonalTailChunk001Sub001Block106Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29087
    = surrogateDiagTailX0RatChunk001Sub001Block106Part004

theorem surrogateDiagonalTailChunk001Sub001Block106Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part004] using hcert

def TailChunk001Sub001Block106Part005SupportExplicit : Finset ℕ :=
  ([29089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part005 : ℚ :=
  (17774644363 : ℚ) / 57536387930846851200

def SurrogateDiagonalTailChunk001Sub001Block106Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29089
    = surrogateDiagTailX0RatChunk001Sub001Block106Part005

theorem surrogateDiagonalTailChunk001Sub001Block106Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part005] using hcert

def TailChunk001Sub001Block106Part006SupportExplicit : Finset ℕ :=
  ([29090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part006 : ℚ :=
  (1058096840725 : ℚ) / 45776694873582501888

def SurrogateDiagonalTailChunk001Sub001Block106Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29090
    = surrogateDiagTailX0RatChunk001Sub001Block106Part006

theorem surrogateDiagonalTailChunk001Sub001Block106Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part006] using hcert

def TailChunk001Sub001Block106Part007SupportExplicit : Finset ℕ :=
  ([29091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part007 : ℚ :=
  (1469100236275 : ℚ) / 88401020290294874112

def SurrogateDiagonalTailChunk001Sub001Block106Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29091
    = surrogateDiagTailX0RatChunk001Sub001Block106Part007

theorem surrogateDiagonalTailChunk001Sub001Block106Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part007] using hcert

def TailChunk001Sub001Block106Part008SupportExplicit : Finset ℕ :=
  ([29093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part008 : ℚ :=
  (205022813575 : ℚ) / 1633097394669604940928

def SurrogateDiagonalTailChunk001Sub001Block106Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29093
    = surrogateDiagTailX0RatChunk001Sub001Block106Part008

theorem surrogateDiagonalTailChunk001Sub001Block106Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part008] using hcert

def TailChunk001Sub001Block106Part009SupportExplicit : Finset ℕ :=
  ([29094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part009 : ℚ :=
  (1486374184225 : ℚ) / 15887061811871612928

def SurrogateDiagonalTailChunk001Sub001Block106Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29094
    = surrogateDiagTailX0RatChunk001Sub001Block106Part009

theorem surrogateDiagonalTailChunk001Sub001Block106Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part009] using hcert

def TailChunk001Sub001Block106Part010SupportExplicit : Finset ℕ :=
  ([29098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block106Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29098
    = surrogateDiagTailX0RatChunk001Sub001Block106Part010

theorem surrogateDiagonalTailChunk001Sub001Block106Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part010] using hcert

def TailChunk001Sub001Block106Part011SupportExplicit : Finset ℕ :=
  ([29099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part011 : ℚ :=
  (1081395957625 : ℚ) / 966794154672844228608

def SurrogateDiagonalTailChunk001Sub001Block106Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29099
    = surrogateDiagTailX0RatChunk001Sub001Block106Part011

theorem surrogateDiagonalTailChunk001Sub001Block106Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part011] using hcert

def TailChunk001Sub001Block106Part012SupportExplicit : Finset ℕ :=
  ([29101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block106Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29101
    = surrogateDiagTailX0RatChunk001Sub001Block106Part012

theorem surrogateDiagonalTailChunk001Sub001Block106Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part012] using hcert

def TailChunk001Sub001Block106Part013SupportExplicit : Finset ℕ :=
  ([29102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block106Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29102
    = surrogateDiagTailX0RatChunk001Sub001Block106Part013

theorem surrogateDiagonalTailChunk001Sub001Block106Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part013] using hcert

def TailChunk001Sub001Block106Part014SupportExplicit : Finset ℕ :=
  ([29103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part014 : ℚ :=
  (5766293552275 : ℚ) / 326416836970621698048

def SurrogateDiagonalTailChunk001Sub001Block106Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29103
    = surrogateDiagTailX0RatChunk001Sub001Block106Part014

theorem surrogateDiagonalTailChunk001Sub001Block106Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part014] using hcert

def TailChunk001Sub001Block106Part015SupportExplicit : Finset ℕ :=
  ([29105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part015 : ℚ :=
  (16946203679 : ℚ) / 5875553022240522240

def SurrogateDiagonalTailChunk001Sub001Block106Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29105
    = surrogateDiagTailX0RatChunk001Sub001Block106Part015

theorem surrogateDiagonalTailChunk001Sub001Block106Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part015] using hcert

def TailChunk001Sub001Block106Part016SupportExplicit : Finset ℕ :=
  ([29107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part016 : ℚ :=
  (69967637525 : ℚ) / 144527224444875343872

def SurrogateDiagonalTailChunk001Sub001Block106Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29107
    = surrogateDiagTailX0RatChunk001Sub001Block106Part016

theorem surrogateDiagonalTailChunk001Sub001Block106Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part016] using hcert

def TailChunk001Sub001Block106Part017SupportExplicit : Finset ℕ :=
  ([29109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part017 : ℚ :=
  (56768614891 : ℚ) / 3070790840224972800

def SurrogateDiagonalTailChunk001Sub001Block106Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29109
    = surrogateDiagTailX0RatChunk001Sub001Block106Part017

theorem surrogateDiagonalTailChunk001Sub001Block106Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part017] using hcert

def TailChunk001Sub001Block106Part018SupportExplicit : Finset ℕ :=
  ([29110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part018 : ℚ :=
  (371384199 : ℚ) / 13115283865600000

def SurrogateDiagonalTailChunk001Sub001Block106Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29110
    = surrogateDiagTailX0RatChunk001Sub001Block106Part018

theorem surrogateDiagonalTailChunk001Sub001Block106Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part018] using hcert

def TailChunk001Sub001Block106Part019SupportExplicit : Finset ℕ :=
  ([29111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part019 : ℚ :=
  (53222349175 : ℚ) / 406210189250742170112

def SurrogateDiagonalTailChunk001Sub001Block106Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29111
    = surrogateDiagTailX0RatChunk001Sub001Block106Part019

theorem surrogateDiagonalTailChunk001Sub001Block106Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part019] using hcert

def TailChunk001Sub001Block106Part020SupportExplicit : Finset ℕ :=
  ([29113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part020 : ℚ :=
  (1082435207725 : ℚ) / 968656507429252295808

def SurrogateDiagonalTailChunk001Sub001Block106Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29113
    = surrogateDiagTailX0RatChunk001Sub001Block106Part020

theorem surrogateDiagonalTailChunk001Sub001Block106Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part020] using hcert

def TailChunk001Sub001Block106Part021SupportExplicit : Finset ℕ :=
  ([29114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block106Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29114
    = surrogateDiagTailX0RatChunk001Sub001Block106Part021

theorem surrogateDiagonalTailChunk001Sub001Block106Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part021] using hcert

def TailChunk001Sub001Block106Part022SupportExplicit : Finset ℕ :=
  ([29117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part022 : ℚ :=
  (731764207 : ℚ) / 1021421446187549400

def SurrogateDiagonalTailChunk001Sub001Block106Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29117
    = surrogateDiagTailX0RatChunk001Sub001Block106Part022

theorem surrogateDiagonalTailChunk001Sub001Block106Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part022] using hcert

def TailChunk001Sub001Block106Part023SupportExplicit : Finset ℕ :=
  ([29118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part023 : ℚ :=
  (187585487 : ℚ) / 2314537285294080

def SurrogateDiagonalTailChunk001Sub001Block106Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29118
    = surrogateDiagTailX0RatChunk001Sub001Block106Part023

theorem surrogateDiagonalTailChunk001Sub001Block106Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part023] using hcert

def TailChunk001Sub001Block106Part024SupportExplicit : Finset ℕ :=
  ([29119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block106Part024 : ℚ :=
  (166449125 : ℚ) / 1099434908147106816

def SurrogateDiagonalTailChunk001Sub001Block106Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29119
    = surrogateDiagTailX0RatChunk001Sub001Block106Part024

theorem surrogateDiagonalTailChunk001Sub001Block106Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block106Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block106Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block106Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block106Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block106Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block106Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block106HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block106Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block106Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block106Part000
    + surrogateDiagTailX0RatChunk001Sub001Block106Part001
    + surrogateDiagTailX0RatChunk001Sub001Block106Part002
    + surrogateDiagTailX0RatChunk001Sub001Block106Part003
    + surrogateDiagTailX0RatChunk001Sub001Block106Part004
    + surrogateDiagTailX0RatChunk001Sub001Block106Part005
    + surrogateDiagTailX0RatChunk001Sub001Block106Part006
    + surrogateDiagTailX0RatChunk001Sub001Block106Part007
    + surrogateDiagTailX0RatChunk001Sub001Block106Part008
    + surrogateDiagTailX0RatChunk001Sub001Block106Part009

def surrogateDiagonalTailChunk001Sub001Block106MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block106Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block106Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block106Part010
    + surrogateDiagTailX0RatChunk001Sub001Block106Part011
    + surrogateDiagTailX0RatChunk001Sub001Block106Part012
    + surrogateDiagTailX0RatChunk001Sub001Block106Part013
    + surrogateDiagTailX0RatChunk001Sub001Block106Part014
    + surrogateDiagTailX0RatChunk001Sub001Block106Part015
    + surrogateDiagTailX0RatChunk001Sub001Block106Part016
    + surrogateDiagTailX0RatChunk001Sub001Block106Part017
    + surrogateDiagTailX0RatChunk001Sub001Block106Part018
    + surrogateDiagTailX0RatChunk001Sub001Block106Part019

def surrogateDiagonalTailChunk001Sub001Block106TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block106Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block106Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block106Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block106Part020
    + surrogateDiagTailX0RatChunk001Sub001Block106Part021
    + surrogateDiagTailX0RatChunk001Sub001Block106Part022
    + surrogateDiagTailX0RatChunk001Sub001Block106Part023
    + surrogateDiagTailX0RatChunk001Sub001Block106Part024

def surrogateDiagonalTailChunk001Sub001Block106Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block106HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block106MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block106TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block106 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block106Part000
    + surrogateDiagTailX0RatChunk001Sub001Block106Part001
    + surrogateDiagTailX0RatChunk001Sub001Block106Part002
    + surrogateDiagTailX0RatChunk001Sub001Block106Part003
    + surrogateDiagTailX0RatChunk001Sub001Block106Part004
    + surrogateDiagTailX0RatChunk001Sub001Block106Part005
    + surrogateDiagTailX0RatChunk001Sub001Block106Part006
    + surrogateDiagTailX0RatChunk001Sub001Block106Part007
    + surrogateDiagTailX0RatChunk001Sub001Block106Part008
    + surrogateDiagTailX0RatChunk001Sub001Block106Part009
    + surrogateDiagTailX0RatChunk001Sub001Block106Part010
    + surrogateDiagTailX0RatChunk001Sub001Block106Part011
    + surrogateDiagTailX0RatChunk001Sub001Block106Part012
    + surrogateDiagTailX0RatChunk001Sub001Block106Part013
    + surrogateDiagTailX0RatChunk001Sub001Block106Part014
    + surrogateDiagTailX0RatChunk001Sub001Block106Part015
    + surrogateDiagTailX0RatChunk001Sub001Block106Part016
    + surrogateDiagTailX0RatChunk001Sub001Block106Part017
    + surrogateDiagTailX0RatChunk001Sub001Block106Part018
    + surrogateDiagTailX0RatChunk001Sub001Block106Part019
    + surrogateDiagTailX0RatChunk001Sub001Block106Part020
    + surrogateDiagTailX0RatChunk001Sub001Block106Part021
    + surrogateDiagTailX0RatChunk001Sub001Block106Part022
    + surrogateDiagTailX0RatChunk001Sub001Block106Part023
    + surrogateDiagTailX0RatChunk001Sub001Block106Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block106_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block106Head + surrogateDiagTailX0RatChunk001Sub001Block106Mid + surrogateDiagTailX0RatChunk001Sub001Block106Tail =
      surrogateDiagTailX0RatChunk001Sub001Block106 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block106Head surrogateDiagTailX0RatChunk001Sub001Block106Mid surrogateDiagTailX0RatChunk001Sub001Block106Tail surrogateDiagTailX0RatChunk001Sub001Block106
  ring

def SurrogateDiagonalTailChunk001Sub001Block106HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block106HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block106Head

def SurrogateDiagonalTailChunk001Sub001Block106MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block106MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block106Mid

def SurrogateDiagonalTailChunk001Sub001Block106TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block106TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block106Tail

theorem surrogateDiagonalTailChunk001Sub001Block106_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block106HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block106MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block106TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block106Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block106 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block106HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block106MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block106TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block106Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block106_eq_head_add_mid_add_tail

/-- Block 107 covers tail-support indices [17675,17700) and q from 29121 to 29162. -/

def TailChunk001Sub001Block107Part000SupportExplicit : Finset ℕ :=
  ([29121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part000 : ℚ :=
  (11107036913 : ℚ) / 553549152921845760

def SurrogateDiagonalTailChunk001Sub001Block107Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29121
    = surrogateDiagTailX0RatChunk001Sub001Block107Part000

theorem surrogateDiagonalTailChunk001Sub001Block107Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part000] using hcert

def TailChunk001Sub001Block107Part001SupportExplicit : Finset ℕ :=
  ([29122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block107Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29122
    = surrogateDiagTailX0RatChunk001Sub001Block107Part001

theorem surrogateDiagonalTailChunk001Sub001Block107Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part001] using hcert

def TailChunk001Sub001Block107Part002SupportExplicit : Finset ℕ :=
  ([29123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block107Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29123
    = surrogateDiagTailX0RatChunk001Sub001Block107Part002

theorem surrogateDiagonalTailChunk001Sub001Block107Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part002] using hcert

def TailChunk001Sub001Block107Part003SupportExplicit : Finset ℕ :=
  ([29126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block107Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29126
    = surrogateDiagTailX0RatChunk001Sub001Block107Part003

theorem surrogateDiagonalTailChunk001Sub001Block107Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part003] using hcert

def TailChunk001Sub001Block107Part004SupportExplicit : Finset ℕ :=
  ([29127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part004 : ℚ :=
  (4719511327975 : ℚ) / 146275586870039543808

def SurrogateDiagonalTailChunk001Sub001Block107Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29127
    = surrogateDiagTailX0RatChunk001Sub001Block107Part004

theorem surrogateDiagonalTailChunk001Sub001Block107Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part004] using hcert

def TailChunk001Sub001Block107Part005SupportExplicit : Finset ℕ :=
  ([29129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block107Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29129
    = surrogateDiagTailX0RatChunk001Sub001Block107Part005

theorem surrogateDiagonalTailChunk001Sub001Block107Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part005] using hcert

def TailChunk001Sub001Block107Part006SupportExplicit : Finset ℕ :=
  ([29130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part006 : ℚ :=
  (2471678347 : ℚ) / 9067211454074880

def SurrogateDiagonalTailChunk001Sub001Block107Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29130
    = surrogateDiagTailX0RatChunk001Sub001Block107Part006

theorem surrogateDiagonalTailChunk001Sub001Block107Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part006] using hcert

def TailChunk001Sub001Block107Part007SupportExplicit : Finset ℕ :=
  ([29131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block107Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29131
    = surrogateDiagTailX0RatChunk001Sub001Block107Part007

theorem surrogateDiagonalTailChunk001Sub001Block107Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part007] using hcert

def TailChunk001Sub001Block107Part008SupportExplicit : Finset ℕ :=
  ([29134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part008 : ℚ :=
  (10851332627 : ℚ) / 1213151936879001600

def SurrogateDiagonalTailChunk001Sub001Block107Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29134
    = surrogateDiagTailX0RatChunk001Sub001Block107Part008

theorem surrogateDiagonalTailChunk001Sub001Block107Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part008] using hcert

def TailChunk001Sub001Block107Part009SupportExplicit : Finset ℕ :=
  ([29135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part009 : ℚ :=
  (2122642709125 : ℚ) / 737477450035320342528

def SurrogateDiagonalTailChunk001Sub001Block107Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29135
    = surrogateDiagTailX0RatChunk001Sub001Block107Part009

theorem surrogateDiagonalTailChunk001Sub001Block107Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part009] using hcert

def TailChunk001Sub001Block107Part010SupportExplicit : Finset ℕ :=
  ([29137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block107Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29137
    = surrogateDiagTailX0RatChunk001Sub001Block107Part010

theorem surrogateDiagonalTailChunk001Sub001Block107Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part010] using hcert

def TailChunk001Sub001Block107Part011SupportExplicit : Finset ℕ :=
  ([29138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part011 : ℚ :=
  (46583275125 : ℚ) / 14663937395511001088

def SurrogateDiagonalTailChunk001Sub001Block107Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29138
    = surrogateDiagTailX0RatChunk001Sub001Block107Part011

theorem surrogateDiagonalTailChunk001Sub001Block107Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part011] using hcert

def TailChunk001Sub001Block107Part012SupportExplicit : Finset ℕ :=
  ([29139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part012 : ℚ :=
  (3607881509 : ℚ) / 1614098087802547200

def SurrogateDiagonalTailChunk001Sub001Block107Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29139
    = surrogateDiagTailX0RatChunk001Sub001Block107Part012

theorem surrogateDiagonalTailChunk001Sub001Block107Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part012] using hcert

def TailChunk001Sub001Block107Part013SupportExplicit : Finset ℕ :=
  ([29141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part013 : ℚ :=
  (2175148501 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk001Sub001Block107Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29141
    = surrogateDiagTailX0RatChunk001Sub001Block107Part013

theorem surrogateDiagonalTailChunk001Sub001Block107Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part013] using hcert

def TailChunk001Sub001Block107Part014SupportExplicit : Finset ℕ :=
  ([29143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part014 : ℚ :=
  (4253117953 : ℚ) / 68810830774272000000

def SurrogateDiagonalTailChunk001Sub001Block107Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29143
    = surrogateDiagTailX0RatChunk001Sub001Block107Part014

theorem surrogateDiagonalTailChunk001Sub001Block107Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part014] using hcert

def TailChunk001Sub001Block107Part015SupportExplicit : Finset ℕ :=
  ([29145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part015 : ℚ :=
  (1297611734275 : ℚ) / 119452343479113351168

def SurrogateDiagonalTailChunk001Sub001Block107Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29145
    = surrogateDiagTailX0RatChunk001Sub001Block107Part015

theorem surrogateDiagonalTailChunk001Sub001Block107Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part015] using hcert

def TailChunk001Sub001Block107Part016SupportExplicit : Finset ℕ :=
  ([29146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part016 : ℚ :=
  (566453015875 : ℚ) / 61596188269835747328

def SurrogateDiagonalTailChunk001Sub001Block107Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29146
    = surrogateDiagTailX0RatChunk001Sub001Block107Part016

theorem surrogateDiagonalTailChunk001Sub001Block107Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part016] using hcert

def TailChunk001Sub001Block107Part017SupportExplicit : Finset ℕ :=
  ([29147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block107Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29147
    = surrogateDiagTailX0RatChunk001Sub001Block107Part017

theorem surrogateDiagonalTailChunk001Sub001Block107Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part017] using hcert

def TailChunk001Sub001Block107Part018SupportExplicit : Finset ℕ :=
  ([29149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part018 : ℚ :=
  (13410221375 : ℚ) / 190187281068118134912

def SurrogateDiagonalTailChunk001Sub001Block107Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29149
    = surrogateDiagTailX0RatChunk001Sub001Block107Part018

theorem surrogateDiagonalTailChunk001Sub001Block107Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part018] using hcert

def TailChunk001Sub001Block107Part019SupportExplicit : Finset ℕ :=
  ([29153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block107Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29153
    = surrogateDiagTailX0RatChunk001Sub001Block107Part019

theorem surrogateDiagonalTailChunk001Sub001Block107Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part019] using hcert

def TailChunk001Sub001Block107Part020SupportExplicit : Finset ℕ :=
  ([29154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part020 : ℚ :=
  (211292267575 : ℚ) / 2798453234979569664

def SurrogateDiagonalTailChunk001Sub001Block107Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29154
    = surrogateDiagTailX0RatChunk001Sub001Block107Part020

theorem surrogateDiagonalTailChunk001Sub001Block107Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part020] using hcert

def TailChunk001Sub001Block107Part021SupportExplicit : Finset ℕ :=
  ([29157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part021 : ℚ :=
  (125025 : ℚ) / 71350589546772608

def SurrogateDiagonalTailChunk001Sub001Block107Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29157
    = surrogateDiagTailX0RatChunk001Sub001Block107Part021

theorem surrogateDiagonalTailChunk001Sub001Block107Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part021] using hcert

def TailChunk001Sub001Block107Part022SupportExplicit : Finset ℕ :=
  ([29158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part022 : ℚ :=
  (3571735009 : ℚ) / 4159103040133171200

def SurrogateDiagonalTailChunk001Sub001Block107Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29158
    = surrogateDiagTailX0RatChunk001Sub001Block107Part022

theorem surrogateDiagonalTailChunk001Sub001Block107Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part022] using hcert

def TailChunk001Sub001Block107Part023SupportExplicit : Finset ℕ :=
  ([29159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part023 : ℚ :=
  (7389505025 : ℚ) / 10234916560666213776

def SurrogateDiagonalTailChunk001Sub001Block107Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29159
    = surrogateDiagTailX0RatChunk001Sub001Block107Part023

theorem surrogateDiagonalTailChunk001Sub001Block107Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part023] using hcert

def TailChunk001Sub001Block107Part024SupportExplicit : Finset ℕ :=
  ([29162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block107Part024 : ℚ :=
  (271803461675 : ℚ) / 30445615998623721024

def SurrogateDiagonalTailChunk001Sub001Block107Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29162
    = surrogateDiagTailX0RatChunk001Sub001Block107Part024

theorem surrogateDiagonalTailChunk001Sub001Block107Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block107Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block107Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block107Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block107Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block107Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block107Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block107HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block107Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block107Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block107Part000
    + surrogateDiagTailX0RatChunk001Sub001Block107Part001
    + surrogateDiagTailX0RatChunk001Sub001Block107Part002
    + surrogateDiagTailX0RatChunk001Sub001Block107Part003
    + surrogateDiagTailX0RatChunk001Sub001Block107Part004
    + surrogateDiagTailX0RatChunk001Sub001Block107Part005
    + surrogateDiagTailX0RatChunk001Sub001Block107Part006
    + surrogateDiagTailX0RatChunk001Sub001Block107Part007
    + surrogateDiagTailX0RatChunk001Sub001Block107Part008
    + surrogateDiagTailX0RatChunk001Sub001Block107Part009

def surrogateDiagonalTailChunk001Sub001Block107MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block107Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block107Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block107Part010
    + surrogateDiagTailX0RatChunk001Sub001Block107Part011
    + surrogateDiagTailX0RatChunk001Sub001Block107Part012
    + surrogateDiagTailX0RatChunk001Sub001Block107Part013
    + surrogateDiagTailX0RatChunk001Sub001Block107Part014
    + surrogateDiagTailX0RatChunk001Sub001Block107Part015
    + surrogateDiagTailX0RatChunk001Sub001Block107Part016
    + surrogateDiagTailX0RatChunk001Sub001Block107Part017
    + surrogateDiagTailX0RatChunk001Sub001Block107Part018
    + surrogateDiagTailX0RatChunk001Sub001Block107Part019

def surrogateDiagonalTailChunk001Sub001Block107TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block107Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block107Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block107Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block107Part020
    + surrogateDiagTailX0RatChunk001Sub001Block107Part021
    + surrogateDiagTailX0RatChunk001Sub001Block107Part022
    + surrogateDiagTailX0RatChunk001Sub001Block107Part023
    + surrogateDiagTailX0RatChunk001Sub001Block107Part024

def surrogateDiagonalTailChunk001Sub001Block107Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block107HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block107MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block107TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block107 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block107Part000
    + surrogateDiagTailX0RatChunk001Sub001Block107Part001
    + surrogateDiagTailX0RatChunk001Sub001Block107Part002
    + surrogateDiagTailX0RatChunk001Sub001Block107Part003
    + surrogateDiagTailX0RatChunk001Sub001Block107Part004
    + surrogateDiagTailX0RatChunk001Sub001Block107Part005
    + surrogateDiagTailX0RatChunk001Sub001Block107Part006
    + surrogateDiagTailX0RatChunk001Sub001Block107Part007
    + surrogateDiagTailX0RatChunk001Sub001Block107Part008
    + surrogateDiagTailX0RatChunk001Sub001Block107Part009
    + surrogateDiagTailX0RatChunk001Sub001Block107Part010
    + surrogateDiagTailX0RatChunk001Sub001Block107Part011
    + surrogateDiagTailX0RatChunk001Sub001Block107Part012
    + surrogateDiagTailX0RatChunk001Sub001Block107Part013
    + surrogateDiagTailX0RatChunk001Sub001Block107Part014
    + surrogateDiagTailX0RatChunk001Sub001Block107Part015
    + surrogateDiagTailX0RatChunk001Sub001Block107Part016
    + surrogateDiagTailX0RatChunk001Sub001Block107Part017
    + surrogateDiagTailX0RatChunk001Sub001Block107Part018
    + surrogateDiagTailX0RatChunk001Sub001Block107Part019
    + surrogateDiagTailX0RatChunk001Sub001Block107Part020
    + surrogateDiagTailX0RatChunk001Sub001Block107Part021
    + surrogateDiagTailX0RatChunk001Sub001Block107Part022
    + surrogateDiagTailX0RatChunk001Sub001Block107Part023
    + surrogateDiagTailX0RatChunk001Sub001Block107Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block107_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block107Head + surrogateDiagTailX0RatChunk001Sub001Block107Mid + surrogateDiagTailX0RatChunk001Sub001Block107Tail =
      surrogateDiagTailX0RatChunk001Sub001Block107 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block107Head surrogateDiagTailX0RatChunk001Sub001Block107Mid surrogateDiagTailX0RatChunk001Sub001Block107Tail surrogateDiagTailX0RatChunk001Sub001Block107
  ring

def SurrogateDiagonalTailChunk001Sub001Block107HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block107HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block107Head

def SurrogateDiagonalTailChunk001Sub001Block107MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block107MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block107Mid

def SurrogateDiagonalTailChunk001Sub001Block107TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block107TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block107Tail

theorem surrogateDiagonalTailChunk001Sub001Block107_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block107HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block107MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block107TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block107Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block107 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block107HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block107MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block107TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block107Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block107_eq_head_add_mid_add_tail

/-- Block 108 covers tail-support indices [17700,17725) and q from 29163 to 29202. -/

def TailChunk001Sub001Block108Part000SupportExplicit : Finset ℕ :=
  ([29163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part000 : ℚ :=
  (1667 : ℚ) / 952124593766400

def SurrogateDiagonalTailChunk001Sub001Block108Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29163
    = surrogateDiagTailX0RatChunk001Sub001Block108Part000

theorem surrogateDiagonalTailChunk001Sub001Block108Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part000] using hcert

def TailChunk001Sub001Block108Part001SupportExplicit : Finset ℕ :=
  ([29165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part001 : ℚ :=
  (35462924125 : ℚ) / 9205822068935496192

def SurrogateDiagonalTailChunk001Sub001Block108Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29165
    = surrogateDiagTailX0RatChunk001Sub001Block108Part001

theorem surrogateDiagonalTailChunk001Sub001Block108Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part001] using hcert

def TailChunk001Sub001Block108Part002SupportExplicit : Finset ℕ :=
  ([29166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part002 : ℚ :=
  (738425033 : ℚ) / 11159941625216640

def SurrogateDiagonalTailChunk001Sub001Block108Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29166
    = surrogateDiagTailX0RatChunk001Sub001Block108Part002

theorem surrogateDiagonalTailChunk001Sub001Block108Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part002] using hcert

def TailChunk001Sub001Block108Part003SupportExplicit : Finset ℕ :=
  ([29167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block108Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29167
    = surrogateDiagTailX0RatChunk001Sub001Block108Part003

theorem surrogateDiagonalTailChunk001Sub001Block108Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part003] using hcert

def TailChunk001Sub001Block108Part004SupportExplicit : Finset ℕ :=
  ([29170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part004 : ℚ :=
  (354639891175 : ℚ) / 15427503302699483136

def SurrogateDiagonalTailChunk001Sub001Block108Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29170
    = surrogateDiagTailX0RatChunk001Sub001Block108Part004

theorem surrogateDiagonalTailChunk001Sub001Block108Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part004] using hcert

def TailChunk001Sub001Block108Part005SupportExplicit : Finset ℕ :=
  ([29171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part005 : ℚ :=
  (760706657 : ℚ) / 4216887592876800000

def SurrogateDiagonalTailChunk001Sub001Block108Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29171
    = surrogateDiagTailX0RatChunk001Sub001Block108Part005

theorem surrogateDiagonalTailChunk001Sub001Block108Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part005] using hcert

def TailChunk001Sub001Block108Part006SupportExplicit : Finset ℕ :=
  ([29173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block108Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29173
    = surrogateDiagTailX0RatChunk001Sub001Block108Part006

theorem surrogateDiagonalTailChunk001Sub001Block108Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part006] using hcert

def TailChunk001Sub001Block108Part007SupportExplicit : Finset ℕ :=
  ([29174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part007 : ℚ :=
  (10732635275 : ℚ) / 6971814401979743232

def SurrogateDiagonalTailChunk001Sub001Block108Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29174
    = surrogateDiagTailX0RatChunk001Sub001Block108Part007

theorem surrogateDiagonalTailChunk001Sub001Block108Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part007] using hcert

def TailChunk001Sub001Block108Part008SupportExplicit : Finset ℕ :=
  ([29177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part008 : ℚ :=
  (35434798175 : ℚ) / 576296088061953995136

def SurrogateDiagonalTailChunk001Sub001Block108Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29177
    = surrogateDiagTailX0RatChunk001Sub001Block108Part008

theorem surrogateDiagonalTailChunk001Sub001Block108Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part008] using hcert

def TailChunk001Sub001Block108Part009SupportExplicit : Finset ℕ :=
  ([29179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block108Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29179
    = surrogateDiagTailX0RatChunk001Sub001Block108Part009

theorem surrogateDiagonalTailChunk001Sub001Block108Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part009] using hcert

def TailChunk001Sub001Block108Part010SupportExplicit : Finset ℕ :=
  ([29181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part010 : ℚ :=
  (5103743917 : ℚ) / 13144819484865331200

def SurrogateDiagonalTailChunk001Sub001Block108Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29181
    = surrogateDiagTailX0RatChunk001Sub001Block108Part010

theorem surrogateDiagonalTailChunk001Sub001Block108Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part010] using hcert

def TailChunk001Sub001Block108Part011SupportExplicit : Finset ℕ :=
  ([29182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block108Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29182
    = surrogateDiagTailX0RatChunk001Sub001Block108Part011

theorem surrogateDiagonalTailChunk001Sub001Block108Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part011] using hcert

def TailChunk001Sub001Block108Part012SupportExplicit : Finset ℕ :=
  ([29183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part012 : ℚ :=
  (12638520749 : ℚ) / 3308027141005574400

def SurrogateDiagonalTailChunk001Sub001Block108Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29183
    = surrogateDiagTailX0RatChunk001Sub001Block108Part012

theorem surrogateDiagonalTailChunk001Sub001Block108Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part012] using hcert

def TailChunk001Sub001Block108Part013SupportExplicit : Finset ℕ :=
  ([29185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part013 : ℚ :=
  (1161600763325 : ℚ) / 267346109632100696064

def SurrogateDiagonalTailChunk001Sub001Block108Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29185
    = surrogateDiagTailX0RatChunk001Sub001Block108Part013

theorem surrogateDiagonalTailChunk001Sub001Block108Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part013] using hcert

def TailChunk001Sub001Block108Part014SupportExplicit : Finset ℕ :=
  ([29186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block108Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29186
    = surrogateDiagTailX0RatChunk001Sub001Block108Part014

theorem surrogateDiagonalTailChunk001Sub001Block108Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part014] using hcert

def TailChunk001Sub001Block108Part015SupportExplicit : Finset ℕ :=
  ([29190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part015 : ℚ :=
  (27979867525 : ℚ) / 89148572660662272

def SurrogateDiagonalTailChunk001Sub001Block108Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29190
    = surrogateDiagTailX0RatChunk001Sub001Block108Part015

theorem surrogateDiagonalTailChunk001Sub001Block108Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part015] using hcert

def TailChunk001Sub001Block108Part016SupportExplicit : Finset ℕ :=
  ([29191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block108Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29191
    = surrogateDiagTailX0RatChunk001Sub001Block108Part016

theorem surrogateDiagonalTailChunk001Sub001Block108Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part016] using hcert

def TailChunk001Sub001Block108Part017SupportExplicit : Finset ℕ :=
  ([29193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part017 : ℚ :=
  (48530277175 : ℚ) / 79159313386591690752

def SurrogateDiagonalTailChunk001Sub001Block108Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29193
    = surrogateDiagTailX0RatChunk001Sub001Block108Part017

theorem surrogateDiagonalTailChunk001Sub001Block108Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part017] using hcert

def TailChunk001Sub001Block108Part018SupportExplicit : Finset ℕ :=
  ([29194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part018 : ℚ :=
  (17697297901 : ℚ) / 3092152799074435200

def SurrogateDiagonalTailChunk001Sub001Block108Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29194
    = surrogateDiagTailX0RatChunk001Sub001Block108Part018

theorem surrogateDiagonalTailChunk001Sub001Block108Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part018] using hcert

def TailChunk001Sub001Block108Part019SupportExplicit : Finset ℕ :=
  ([29195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part019 : ℚ :=
  (2131390707625 : ℚ) / 743572272605920708608

def SurrogateDiagonalTailChunk001Sub001Block108Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29195
    = surrogateDiagTailX0RatChunk001Sub001Block108Part019

theorem surrogateDiagonalTailChunk001Sub001Block108Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part019] using hcert

def TailChunk001Sub001Block108Part020SupportExplicit : Finset ℕ :=
  ([29197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part020 : ℚ :=
  (253107552175 : ℚ) / 95163727500879593472

def SurrogateDiagonalTailChunk001Sub001Block108Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29197
    = surrogateDiagTailX0RatChunk001Sub001Block108Part020

theorem surrogateDiagonalTailChunk001Sub001Block108Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part020] using hcert

def TailChunk001Sub001Block108Part021SupportExplicit : Finset ℕ :=
  ([29198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part021 : ℚ :=
  (159142634825 : ℚ) / 41085944493609083904

def SurrogateDiagonalTailChunk001Sub001Block108Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29198
    = surrogateDiagTailX0RatChunk001Sub001Block108Part021

theorem surrogateDiagonalTailChunk001Sub001Block108Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part021] using hcert

def TailChunk001Sub001Block108Part022SupportExplicit : Finset ℕ :=
  ([29199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part022 : ℚ :=
  (41675 : ℚ) / 23920878947751936

def SurrogateDiagonalTailChunk001Sub001Block108Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29199
    = surrogateDiagTailX0RatChunk001Sub001Block108Part022

theorem surrogateDiagonalTailChunk001Sub001Block108Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part022] using hcert

def TailChunk001Sub001Block108Part023SupportExplicit : Finset ℕ :=
  ([29201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block108Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29201
    = surrogateDiagTailX0RatChunk001Sub001Block108Part023

theorem surrogateDiagonalTailChunk001Sub001Block108Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part023] using hcert

def TailChunk001Sub001Block108Part024SupportExplicit : Finset ℕ :=
  ([29202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block108Part024 : ℚ :=
  (507670091 : ℚ) / 6561518889369600

def SurrogateDiagonalTailChunk001Sub001Block108Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29202
    = surrogateDiagTailX0RatChunk001Sub001Block108Part024

theorem surrogateDiagonalTailChunk001Sub001Block108Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block108Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block108Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block108Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block108Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block108Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block108Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block108HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block108Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block108Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block108Part000
    + surrogateDiagTailX0RatChunk001Sub001Block108Part001
    + surrogateDiagTailX0RatChunk001Sub001Block108Part002
    + surrogateDiagTailX0RatChunk001Sub001Block108Part003
    + surrogateDiagTailX0RatChunk001Sub001Block108Part004
    + surrogateDiagTailX0RatChunk001Sub001Block108Part005
    + surrogateDiagTailX0RatChunk001Sub001Block108Part006
    + surrogateDiagTailX0RatChunk001Sub001Block108Part007
    + surrogateDiagTailX0RatChunk001Sub001Block108Part008
    + surrogateDiagTailX0RatChunk001Sub001Block108Part009

def surrogateDiagonalTailChunk001Sub001Block108MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block108Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block108Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block108Part010
    + surrogateDiagTailX0RatChunk001Sub001Block108Part011
    + surrogateDiagTailX0RatChunk001Sub001Block108Part012
    + surrogateDiagTailX0RatChunk001Sub001Block108Part013
    + surrogateDiagTailX0RatChunk001Sub001Block108Part014
    + surrogateDiagTailX0RatChunk001Sub001Block108Part015
    + surrogateDiagTailX0RatChunk001Sub001Block108Part016
    + surrogateDiagTailX0RatChunk001Sub001Block108Part017
    + surrogateDiagTailX0RatChunk001Sub001Block108Part018
    + surrogateDiagTailX0RatChunk001Sub001Block108Part019

def surrogateDiagonalTailChunk001Sub001Block108TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block108Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block108Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block108Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block108Part020
    + surrogateDiagTailX0RatChunk001Sub001Block108Part021
    + surrogateDiagTailX0RatChunk001Sub001Block108Part022
    + surrogateDiagTailX0RatChunk001Sub001Block108Part023
    + surrogateDiagTailX0RatChunk001Sub001Block108Part024

def surrogateDiagonalTailChunk001Sub001Block108Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block108HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block108MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block108TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block108 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block108Part000
    + surrogateDiagTailX0RatChunk001Sub001Block108Part001
    + surrogateDiagTailX0RatChunk001Sub001Block108Part002
    + surrogateDiagTailX0RatChunk001Sub001Block108Part003
    + surrogateDiagTailX0RatChunk001Sub001Block108Part004
    + surrogateDiagTailX0RatChunk001Sub001Block108Part005
    + surrogateDiagTailX0RatChunk001Sub001Block108Part006
    + surrogateDiagTailX0RatChunk001Sub001Block108Part007
    + surrogateDiagTailX0RatChunk001Sub001Block108Part008
    + surrogateDiagTailX0RatChunk001Sub001Block108Part009
    + surrogateDiagTailX0RatChunk001Sub001Block108Part010
    + surrogateDiagTailX0RatChunk001Sub001Block108Part011
    + surrogateDiagTailX0RatChunk001Sub001Block108Part012
    + surrogateDiagTailX0RatChunk001Sub001Block108Part013
    + surrogateDiagTailX0RatChunk001Sub001Block108Part014
    + surrogateDiagTailX0RatChunk001Sub001Block108Part015
    + surrogateDiagTailX0RatChunk001Sub001Block108Part016
    + surrogateDiagTailX0RatChunk001Sub001Block108Part017
    + surrogateDiagTailX0RatChunk001Sub001Block108Part018
    + surrogateDiagTailX0RatChunk001Sub001Block108Part019
    + surrogateDiagTailX0RatChunk001Sub001Block108Part020
    + surrogateDiagTailX0RatChunk001Sub001Block108Part021
    + surrogateDiagTailX0RatChunk001Sub001Block108Part022
    + surrogateDiagTailX0RatChunk001Sub001Block108Part023
    + surrogateDiagTailX0RatChunk001Sub001Block108Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block108_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block108Head + surrogateDiagTailX0RatChunk001Sub001Block108Mid + surrogateDiagTailX0RatChunk001Sub001Block108Tail =
      surrogateDiagTailX0RatChunk001Sub001Block108 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block108Head surrogateDiagTailX0RatChunk001Sub001Block108Mid surrogateDiagTailX0RatChunk001Sub001Block108Tail surrogateDiagTailX0RatChunk001Sub001Block108
  ring

def SurrogateDiagonalTailChunk001Sub001Block108HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block108HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block108Head

def SurrogateDiagonalTailChunk001Sub001Block108MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block108MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block108Mid

def SurrogateDiagonalTailChunk001Sub001Block108TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block108TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block108Tail

theorem surrogateDiagonalTailChunk001Sub001Block108_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block108HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block108MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block108TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block108Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block108 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block108HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block108MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block108TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block108Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block108_eq_head_add_mid_add_tail

/-- Block 109 covers tail-support indices [17725,17750) and q from 29203 to 29243. -/

def TailChunk001Sub001Block109Part000SupportExplicit : Finset ℕ :=
  ([29203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part000 : ℚ :=
  (210480815275 : ℚ) / 294918752295206387712

def SurrogateDiagonalTailChunk001Sub001Block109Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29203
    = surrogateDiagTailX0RatChunk001Sub001Block109Part000

theorem surrogateDiagonalTailChunk001Sub001Block109Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part000] using hcert

def TailChunk001Sub001Block109Part001SupportExplicit : Finset ℕ :=
  ([29206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part001 : ℚ :=
  (234865869025 : ℚ) / 88808787539227312128

def SurrogateDiagonalTailChunk001Sub001Block109Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29206
    = surrogateDiagTailX0RatChunk001Sub001Block109Part001

theorem surrogateDiagonalTailChunk001Sub001Block109Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part001] using hcert

def TailChunk001Sub001Block109Part002SupportExplicit : Finset ℕ :=
  ([29207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block109Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29207
    = surrogateDiagTailX0RatChunk001Sub001Block109Part002

theorem surrogateDiagonalTailChunk001Sub001Block109Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part002] using hcert

def TailChunk001Sub001Block109Part003SupportExplicit : Finset ℕ :=
  ([29209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block109Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29209
    = surrogateDiagTailX0RatChunk001Sub001Block109Part003

theorem surrogateDiagonalTailChunk001Sub001Block109Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part003] using hcert

def TailChunk001Sub001Block109Part004SupportExplicit : Finset ℕ :=
  ([29210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part004 : ℚ :=
  (332360809925 : ℚ) / 18897734026969104384

def SurrogateDiagonalTailChunk001Sub001Block109Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29210
    = surrogateDiagTailX0RatChunk001Sub001Block109Part004

theorem surrogateDiagonalTailChunk001Sub001Block109Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part004] using hcert

def TailChunk001Sub001Block109Part005SupportExplicit : Finset ℕ :=
  ([29211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part005 : ℚ :=
  (159477105125 : ℚ) / 15081959800516902912

def SurrogateDiagonalTailChunk001Sub001Block109Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29211
    = surrogateDiagTailX0RatChunk001Sub001Block109Part005

theorem surrogateDiagonalTailChunk001Sub001Block109Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part005] using hcert

def TailChunk001Sub001Block109Part006SupportExplicit : Finset ℕ :=
  ([29213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part006 : ℚ :=
  (6642179 : ℚ) / 106747767389060928

def SurrogateDiagonalTailChunk001Sub001Block109Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29213
    = surrogateDiagTailX0RatChunk001Sub001Block109Part006

theorem surrogateDiagonalTailChunk001Sub001Block109Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part006] using hcert

def TailChunk001Sub001Block109Part007SupportExplicit : Finset ℕ :=
  ([29215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part007 : ℚ :=
  (711436902375 : ℚ) / 248537416736008247296

def SurrogateDiagonalTailChunk001Sub001Block109Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29215
    = surrogateDiagTailX0RatChunk001Sub001Block109Part007

theorem surrogateDiagonalTailChunk001Sub001Block109Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part007] using hcert

def TailChunk001Sub001Block109Part008SupportExplicit : Finset ℕ :=
  ([29217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part008 : ℚ :=
  (41675 : ℚ) / 23979924594343296

def SurrogateDiagonalTailChunk001Sub001Block109Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29217
    = surrogateDiagTailX0RatChunk001Sub001Block109Part008

theorem surrogateDiagonalTailChunk001Sub001Block109Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part008] using hcert

def TailChunk001Sub001Block109Part009SupportExplicit : Finset ℕ :=
  ([29218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part009 : ℚ :=
  (272845253375 : ℚ) / 30680263206758136384

def SurrogateDiagonalTailChunk001Sub001Block109Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29218
    = surrogateDiagTailX0RatChunk001Sub001Block109Part009

theorem surrogateDiagonalTailChunk001Sub001Block109Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part009] using hcert

def TailChunk001Sub001Block109Part010SupportExplicit : Finset ℕ :=
  ([29219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part010 : ℚ :=
  (3510550133 : ℚ) / 33835565749885977600

def SurrogateDiagonalTailChunk001Sub001Block109Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29219
    = surrogateDiagTailX0RatChunk001Sub001Block109Part010

theorem surrogateDiagonalTailChunk001Sub001Block109Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part010] using hcert

def TailChunk001Sub001Block109Part011SupportExplicit : Finset ℕ :=
  ([29221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block109Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29221
    = surrogateDiagTailX0RatChunk001Sub001Block109Part011

theorem surrogateDiagonalTailChunk001Sub001Block109Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part011] using hcert

def TailChunk001Sub001Block109Part012SupportExplicit : Finset ℕ :=
  ([29222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part012 : ℚ :=
  (113292604925 : ℚ) / 45659564381929734144

def SurrogateDiagonalTailChunk001Sub001Block109Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29222
    = surrogateDiagTailX0RatChunk001Sub001Block109Part012

theorem surrogateDiagonalTailChunk001Sub001Block109Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part012] using hcert

def TailChunk001Sub001Block109Part013SupportExplicit : Finset ℕ :=
  ([29226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part013 : ℚ :=
  (5931725263 : ℚ) / 90016615020659520

def SurrogateDiagonalTailChunk001Sub001Block109Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29226
    = surrogateDiagTailX0RatChunk001Sub001Block109Part013

theorem surrogateDiagonalTailChunk001Sub001Block109Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part013] using hcert

def TailChunk001Sub001Block109Part014SupportExplicit : Finset ℕ :=
  ([29227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part014 : ℚ :=
  (8847432199 : ℚ) / 12443402283044044800

def SurrogateDiagonalTailChunk001Sub001Block109Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29227
    = surrogateDiagTailX0RatChunk001Sub001Block109Part014

theorem surrogateDiagonalTailChunk001Sub001Block109Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part014] using hcert

def TailChunk001Sub001Block109Part015SupportExplicit : Finset ℕ :=
  ([29229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part015 : ℚ :=
  (125025 : ℚ) / 72058047122288768

def SurrogateDiagonalTailChunk001Sub001Block109Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29229
    = surrogateDiagTailX0RatChunk001Sub001Block109Part015

theorem surrogateDiagonalTailChunk001Sub001Block109Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part015] using hcert

def TailChunk001Sub001Block109Part016SupportExplicit : Finset ℕ :=
  ([29230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part016 : ℚ :=
  (635397166075 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk001Sub001Block109Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29230
    = surrogateDiagTailX0RatChunk001Sub001Block109Part016

theorem surrogateDiagonalTailChunk001Sub001Block109Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part016] using hcert

def TailChunk001Sub001Block109Part017SupportExplicit : Finset ℕ :=
  ([29231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block109Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29231
    = surrogateDiagTailX0RatChunk001Sub001Block109Part017

theorem surrogateDiagonalTailChunk001Sub001Block109Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part017] using hcert

def TailChunk001Sub001Block109Part018SupportExplicit : Finset ℕ :=
  ([29233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part018 : ℚ :=
  (8186709811 : ℚ) / 12146259806208000000

def SurrogateDiagonalTailChunk001Sub001Block109Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29233
    = surrogateDiagTailX0RatChunk001Sub001Block109Part018

theorem surrogateDiagonalTailChunk001Sub001Block109Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part018] using hcert

def TailChunk001Sub001Block109Part019SupportExplicit : Finset ℕ :=
  ([29234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part019 : ℚ :=
  (4405534963 : ℚ) / 4135851647504515200

def SurrogateDiagonalTailChunk001Sub001Block109Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29234
    = surrogateDiagTailX0RatChunk001Sub001Block109Part019

theorem surrogateDiagonalTailChunk001Sub001Block109Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part019] using hcert

def TailChunk001Sub001Block109Part020SupportExplicit : Finset ℕ :=
  ([29235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part020 : ℚ :=
  (356449712875 : ℚ) / 36870805512462139392

def SurrogateDiagonalTailChunk001Sub001Block109Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29235
    = surrogateDiagTailX0RatChunk001Sub001Block109Part020

theorem surrogateDiagonalTailChunk001Sub001Block109Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part020] using hcert

def TailChunk001Sub001Block109Part021SupportExplicit : Finset ℕ :=
  ([29238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part021 : ℚ :=
  (1824207881 : ℚ) / 19087362957249600

def SurrogateDiagonalTailChunk001Sub001Block109Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29238
    = surrogateDiagTailX0RatChunk001Sub001Block109Part021

theorem surrogateDiagonalTailChunk001Sub001Block109Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part021] using hcert

def TailChunk001Sub001Block109Part022SupportExplicit : Finset ℕ :=
  ([29239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part022 : ℚ :=
  (1091810958625 : ℚ) / 985539012317371957248

def SurrogateDiagonalTailChunk001Sub001Block109Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29239
    = surrogateDiagTailX0RatChunk001Sub001Block109Part022

theorem surrogateDiagonalTailChunk001Sub001Block109Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part022] using hcert

def TailChunk001Sub001Block109Part023SupportExplicit : Finset ℕ :=
  ([29242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block109Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29242
    = surrogateDiagTailX0RatChunk001Sub001Block109Part023

theorem surrogateDiagonalTailChunk001Sub001Block109Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part023] using hcert

def TailChunk001Sub001Block109Part024SupportExplicit : Finset ℕ :=
  ([29243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block109Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block109Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29243
    = surrogateDiagTailX0RatChunk001Sub001Block109Part024

theorem surrogateDiagonalTailChunk001Sub001Block109Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block109Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block109Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block109Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block109Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block109Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block109Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block109HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block109Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block109Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block109Part000
    + surrogateDiagTailX0RatChunk001Sub001Block109Part001
    + surrogateDiagTailX0RatChunk001Sub001Block109Part002
    + surrogateDiagTailX0RatChunk001Sub001Block109Part003
    + surrogateDiagTailX0RatChunk001Sub001Block109Part004
    + surrogateDiagTailX0RatChunk001Sub001Block109Part005
    + surrogateDiagTailX0RatChunk001Sub001Block109Part006
    + surrogateDiagTailX0RatChunk001Sub001Block109Part007
    + surrogateDiagTailX0RatChunk001Sub001Block109Part008
    + surrogateDiagTailX0RatChunk001Sub001Block109Part009

def surrogateDiagonalTailChunk001Sub001Block109MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block109Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block109Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block109Part010
    + surrogateDiagTailX0RatChunk001Sub001Block109Part011
    + surrogateDiagTailX0RatChunk001Sub001Block109Part012
    + surrogateDiagTailX0RatChunk001Sub001Block109Part013
    + surrogateDiagTailX0RatChunk001Sub001Block109Part014
    + surrogateDiagTailX0RatChunk001Sub001Block109Part015
    + surrogateDiagTailX0RatChunk001Sub001Block109Part016
    + surrogateDiagTailX0RatChunk001Sub001Block109Part017
    + surrogateDiagTailX0RatChunk001Sub001Block109Part018
    + surrogateDiagTailX0RatChunk001Sub001Block109Part019

def surrogateDiagonalTailChunk001Sub001Block109TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block109Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block109Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block109Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block109Part020
    + surrogateDiagTailX0RatChunk001Sub001Block109Part021
    + surrogateDiagTailX0RatChunk001Sub001Block109Part022
    + surrogateDiagTailX0RatChunk001Sub001Block109Part023
    + surrogateDiagTailX0RatChunk001Sub001Block109Part024

def surrogateDiagonalTailChunk001Sub001Block109Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block109HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block109MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block109TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block109 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block109Part000
    + surrogateDiagTailX0RatChunk001Sub001Block109Part001
    + surrogateDiagTailX0RatChunk001Sub001Block109Part002
    + surrogateDiagTailX0RatChunk001Sub001Block109Part003
    + surrogateDiagTailX0RatChunk001Sub001Block109Part004
    + surrogateDiagTailX0RatChunk001Sub001Block109Part005
    + surrogateDiagTailX0RatChunk001Sub001Block109Part006
    + surrogateDiagTailX0RatChunk001Sub001Block109Part007
    + surrogateDiagTailX0RatChunk001Sub001Block109Part008
    + surrogateDiagTailX0RatChunk001Sub001Block109Part009
    + surrogateDiagTailX0RatChunk001Sub001Block109Part010
    + surrogateDiagTailX0RatChunk001Sub001Block109Part011
    + surrogateDiagTailX0RatChunk001Sub001Block109Part012
    + surrogateDiagTailX0RatChunk001Sub001Block109Part013
    + surrogateDiagTailX0RatChunk001Sub001Block109Part014
    + surrogateDiagTailX0RatChunk001Sub001Block109Part015
    + surrogateDiagTailX0RatChunk001Sub001Block109Part016
    + surrogateDiagTailX0RatChunk001Sub001Block109Part017
    + surrogateDiagTailX0RatChunk001Sub001Block109Part018
    + surrogateDiagTailX0RatChunk001Sub001Block109Part019
    + surrogateDiagTailX0RatChunk001Sub001Block109Part020
    + surrogateDiagTailX0RatChunk001Sub001Block109Part021
    + surrogateDiagTailX0RatChunk001Sub001Block109Part022
    + surrogateDiagTailX0RatChunk001Sub001Block109Part023
    + surrogateDiagTailX0RatChunk001Sub001Block109Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block109_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block109Head + surrogateDiagTailX0RatChunk001Sub001Block109Mid + surrogateDiagTailX0RatChunk001Sub001Block109Tail =
      surrogateDiagTailX0RatChunk001Sub001Block109 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block109Head surrogateDiagTailX0RatChunk001Sub001Block109Mid surrogateDiagTailX0RatChunk001Sub001Block109Tail surrogateDiagTailX0RatChunk001Sub001Block109
  ring

def SurrogateDiagonalTailChunk001Sub001Block109HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block109HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block109Head

def SurrogateDiagonalTailChunk001Sub001Block109MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block109MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block109Mid

def SurrogateDiagonalTailChunk001Sub001Block109TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block109TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block109Tail

theorem surrogateDiagonalTailChunk001Sub001Block109_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block109HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block109MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block109TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block109Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block109 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block109HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block109MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block109TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block109Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block109_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
