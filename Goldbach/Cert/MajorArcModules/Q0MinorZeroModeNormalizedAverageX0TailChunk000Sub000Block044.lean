import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [44,45). -/

/- Block 044 covers tail-support indices [1100,1125) and q from 1866 to 1903. -/

def TailChunk000Sub000Block044Part000SupportExplicit : Finset ℕ :=
  ([1866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part000 : ℚ :=
  (4097432621 : ℚ) / 7389645633600

def SurrogateDiagonalTailChunk000Sub000Block044Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1866
    = surrogateDiagTailX0RatChunk000Sub000Block044Part000

theorem surrogateDiagonalTailChunk000Sub000Block044Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part000] using hcert

def TailChunk000Sub000Block044Part001SupportExplicit : Finset ℕ :=
  ([1867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part001 : ℚ :=
  (72589473425 : ℚ) / 3368456219292552

def SurrogateDiagonalTailChunk000Sub000Block044Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1867
    = surrogateDiagTailX0RatChunk000Sub000Block044Part001

theorem surrogateDiagonalTailChunk000Sub000Block044Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part001] using hcert

def TailChunk000Sub000Block044Part002SupportExplicit : Finset ℕ :=
  ([1869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part002 : ℚ :=
  (43365635375 : ℚ) / 388680313798656

def SurrogateDiagonalTailChunk000Sub000Block044Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1869
    = surrogateDiagTailX0RatChunk000Sub000Block044Part002

theorem surrogateDiagonalTailChunk000Sub000Block044Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part002] using hcert

def TailChunk000Sub000Block044Part003SupportExplicit : Finset ℕ :=
  ([1870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part003 : ℚ :=
  (8637842101 : ℚ) / 16780571443200

def SurrogateDiagonalTailChunk000Sub000Block044Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1870
    = surrogateDiagTailX0RatChunk000Sub000Block044Part003

theorem surrogateDiagonalTailChunk000Sub000Block044Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part003] using hcert

def TailChunk000Sub000Block044Part004SupportExplicit : Finset ℕ :=
  ([1871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part004 : ℚ :=
  (17499704359 : ℚ) / 1223075527192200

def SurrogateDiagonalTailChunk000Sub000Block044Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1871
    = surrogateDiagTailX0RatChunk000Sub000Block044Part004

theorem surrogateDiagonalTailChunk000Sub000Block044Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part004] using hcert

def TailChunk000Sub000Block044Part005SupportExplicit : Finset ℕ :=
  ([1873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part005 : ℚ :=
  (73056786425 : ℚ) / 3411989822472192

def SurrogateDiagonalTailChunk000Sub000Block044Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1873
    = surrogateDiagTailX0RatChunk000Sub000Block044Part005

theorem surrogateDiagonalTailChunk000Sub000Block044Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part005] using hcert

def TailChunk000Sub000Block044Part006SupportExplicit : Finset ℕ :=
  ([1874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part006 : ℚ :=
  (137072910125 : ℚ) / 959622137570304

def SurrogateDiagonalTailChunk000Sub000Block044Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1874
    = surrogateDiagTailX0RatChunk000Sub000Block044Part006

theorem surrogateDiagonalTailChunk000Sub000Block044Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part006] using hcert

def TailChunk000Sub000Block044Part007SupportExplicit : Finset ℕ :=
  ([1877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part007 : ℚ :=
  (4491989475 : ℚ) / 210688514130304

def SurrogateDiagonalTailChunk000Sub000Block044Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1877
    = surrogateDiagTailX0RatChunk000Sub000Block044Part007

theorem surrogateDiagonalTailChunk000Sub000Block044Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part007] using hcert

def TailChunk000Sub000Block044Part008SupportExplicit : Finset ℕ :=
  ([1878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part008 : ℚ :=
  (189263808325 : ℚ) / 379109980274688

def SurrogateDiagonalTailChunk000Sub000Block044Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1878
    = surrogateDiagTailX0RatChunk000Sub000Block044Part008

theorem surrogateDiagonalTailChunk000Sub000Block044Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part008] using hcert

def TailChunk000Sub000Block044Part009SupportExplicit : Finset ℕ :=
  ([1879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part009 : ℚ :=
  (441241858975 : ℚ) / 31103496329014728

def SurrogateDiagonalTailChunk000Sub000Block044Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1879
    = surrogateDiagTailX0RatChunk000Sub000Block044Part009

theorem surrogateDiagonalTailChunk000Sub000Block044Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part009] using hcert

def TailChunk000Sub000Block044Part010SupportExplicit : Finset ℕ :=
  ([1882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part010 : ℚ :=
  (1105965769 : ℚ) / 7809051097920

def SurrogateDiagonalTailChunk000Sub000Block044Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1882
    = surrogateDiagTailX0RatChunk000Sub000Block044Part010

theorem surrogateDiagonalTailChunk000Sub000Block044Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part010] using hcert

def TailChunk000Sub000Block044Part011SupportExplicit : Finset ℕ :=
  ([1883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part011 : ℚ :=
  (8337473575 : ℚ) / 249514755692544

def SurrogateDiagonalTailChunk000Sub000Block044Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1883
    = surrogateDiagTailX0RatChunk000Sub000Block044Part011

theorem surrogateDiagonalTailChunk000Sub000Block044Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part011] using hcert

def TailChunk000Sub000Block044Part012SupportExplicit : Finset ℕ :=
  ([1885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part012 : ℚ :=
  (174681194675 : ℚ) / 4079377893556224

def SurrogateDiagonalTailChunk000Sub000Block044Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1885
    = surrogateDiagTailX0RatChunk000Sub000Block044Part012

theorem surrogateDiagonalTailChunk000Sub000Block044Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part012] using hcert

def TailChunk000Sub000Block044Part013SupportExplicit : Finset ℕ :=
  ([1886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part013 : ℚ :=
  (10418232373 : ℚ) / 59981529907200

def SurrogateDiagonalTailChunk000Sub000Block044Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1886
    = surrogateDiagTailX0RatChunk000Sub000Block044Part013

theorem surrogateDiagonalTailChunk000Sub000Block044Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part013] using hcert

def TailChunk000Sub000Block044Part014SupportExplicit : Finset ℕ :=
  ([1887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part014 : ℚ :=
  (95696289925 : ℚ) / 1100973292388352

def SurrogateDiagonalTailChunk000Sub000Block044Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1887
    = surrogateDiagTailX0RatChunk000Sub000Block044Part014

theorem surrogateDiagonalTailChunk000Sub000Block044Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part014] using hcert

def TailChunk000Sub000Block044Part015SupportExplicit : Finset ℕ :=
  ([1889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part015 : ℚ :=
  (222930854475 : ℚ) / 10590429268934656

def SurrogateDiagonalTailChunk000Sub000Block044Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1889
    = surrogateDiagTailX0RatChunk000Sub000Block044Part015

theorem surrogateDiagonalTailChunk000Sub000Block044Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part015] using hcert

def TailChunk000Sub000Block044Part016SupportExplicit : Finset ℕ :=
  ([1891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part016 : ℚ :=
  (28203607 : ℚ) / 1166633280000

def SurrogateDiagonalTailChunk000Sub000Block044Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1891
    = surrogateDiagTailX0RatChunk000Sub000Block044Part016

theorem surrogateDiagonalTailChunk000Sub000Block044Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part016] using hcert

def TailChunk000Sub000Block044Part017SupportExplicit : Finset ℕ :=
  ([1893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part017 : ℚ :=
  (497087749 : ℚ) / 9003492338400

def SurrogateDiagonalTailChunk000Sub000Block044Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1893
    = surrogateDiagTailX0RatChunk000Sub000Block044Part017

theorem surrogateDiagonalTailChunk000Sub000Block044Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part017] using hcert

def TailChunk000Sub000Block044Part018SupportExplicit : Finset ℕ :=
  ([1894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part018 : ℚ :=
  (111989023875 : ℚ) / 667529018321176

def SurrogateDiagonalTailChunk000Sub000Block044Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1894
    = surrogateDiagTailX0RatChunk000Sub000Block044Part018

theorem surrogateDiagonalTailChunk000Sub000Block044Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part018] using hcert

def TailChunk000Sub000Block044Part019SupportExplicit : Finset ℕ :=
  ([1895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part019 : ℚ :=
  (519298608925 : ℚ) / 13068749199034368

def SurrogateDiagonalTailChunk000Sub000Block044Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1895
    = surrogateDiagTailX0RatChunk000Sub000Block044Part019

theorem surrogateDiagonalTailChunk000Sub000Block044Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part019] using hcert

def TailChunk000Sub000Block044Part020SupportExplicit : Finset ℕ :=
  ([1897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part020 : ℚ :=
  (69430819 : ℚ) / 2126189152800

def SurrogateDiagonalTailChunk000Sub000Block044Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1897
    = surrogateDiagTailX0RatChunk000Sub000Block044Part020

theorem surrogateDiagonalTailChunk000Sub000Block044Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part020] using hcert

def TailChunk000Sub000Block044Part021SupportExplicit : Finset ℕ :=
  ([1898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part021 : ℚ :=
  (33752642275 : ℚ) / 154824369242112

def SurrogateDiagonalTailChunk000Sub000Block044Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1898
    = surrogateDiagTailX0RatChunk000Sub000Block044Part021

theorem surrogateDiagonalTailChunk000Sub000Block044Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part021] using hcert

def TailChunk000Sub000Block044Part022SupportExplicit : Finset ℕ :=
  ([1901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part022 : ℚ :=
  (18065391199 : ℚ) / 1303470642000000

def SurrogateDiagonalTailChunk000Sub000Block044Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1901
    = surrogateDiagTailX0RatChunk000Sub000Block044Part022

theorem surrogateDiagonalTailChunk000Sub000Block044Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part022] using hcert

def TailChunk000Sub000Block044Part023SupportExplicit : Finset ℕ :=
  ([1902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part023 : ℚ :=
  (106427269475 : ℚ) / 199464299602944

def SurrogateDiagonalTailChunk000Sub000Block044Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1902
    = surrogateDiagTailX0RatChunk000Sub000Block044Part023

theorem surrogateDiagonalTailChunk000Sub000Block044Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part023] using hcert

def TailChunk000Sub000Block044Part024SupportExplicit : Finset ℕ :=
  ([1903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block044Part024 : ℚ :=
  (1211993519 : ℚ) / 43769404930560

def SurrogateDiagonalTailChunk000Sub000Block044Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1903
    = surrogateDiagTailX0RatChunk000Sub000Block044Part024

theorem surrogateDiagonalTailChunk000Sub000Block044Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block044Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block044Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block044Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block044Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block044Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block044Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block044HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block044Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block044Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block044Part000
    + surrogateDiagTailX0RatChunk000Sub000Block044Part001
    + surrogateDiagTailX0RatChunk000Sub000Block044Part002
    + surrogateDiagTailX0RatChunk000Sub000Block044Part003
    + surrogateDiagTailX0RatChunk000Sub000Block044Part004
    + surrogateDiagTailX0RatChunk000Sub000Block044Part005
    + surrogateDiagTailX0RatChunk000Sub000Block044Part006
    + surrogateDiagTailX0RatChunk000Sub000Block044Part007
    + surrogateDiagTailX0RatChunk000Sub000Block044Part008
    + surrogateDiagTailX0RatChunk000Sub000Block044Part009

def surrogateDiagonalTailChunk000Sub000Block044MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block044Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block044Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block044Part010
    + surrogateDiagTailX0RatChunk000Sub000Block044Part011
    + surrogateDiagTailX0RatChunk000Sub000Block044Part012
    + surrogateDiagTailX0RatChunk000Sub000Block044Part013
    + surrogateDiagTailX0RatChunk000Sub000Block044Part014
    + surrogateDiagTailX0RatChunk000Sub000Block044Part015
    + surrogateDiagTailX0RatChunk000Sub000Block044Part016
    + surrogateDiagTailX0RatChunk000Sub000Block044Part017
    + surrogateDiagTailX0RatChunk000Sub000Block044Part018
    + surrogateDiagTailX0RatChunk000Sub000Block044Part019

def surrogateDiagonalTailChunk000Sub000Block044TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block044Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block044Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block044Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block044Part020
    + surrogateDiagTailX0RatChunk000Sub000Block044Part021
    + surrogateDiagTailX0RatChunk000Sub000Block044Part022
    + surrogateDiagTailX0RatChunk000Sub000Block044Part023
    + surrogateDiagTailX0RatChunk000Sub000Block044Part024

def surrogateDiagonalTailChunk000Sub000Block044Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block044HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block044MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block044TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block044 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block044Part000
    + surrogateDiagTailX0RatChunk000Sub000Block044Part001
    + surrogateDiagTailX0RatChunk000Sub000Block044Part002
    + surrogateDiagTailX0RatChunk000Sub000Block044Part003
    + surrogateDiagTailX0RatChunk000Sub000Block044Part004
    + surrogateDiagTailX0RatChunk000Sub000Block044Part005
    + surrogateDiagTailX0RatChunk000Sub000Block044Part006
    + surrogateDiagTailX0RatChunk000Sub000Block044Part007
    + surrogateDiagTailX0RatChunk000Sub000Block044Part008
    + surrogateDiagTailX0RatChunk000Sub000Block044Part009
    + surrogateDiagTailX0RatChunk000Sub000Block044Part010
    + surrogateDiagTailX0RatChunk000Sub000Block044Part011
    + surrogateDiagTailX0RatChunk000Sub000Block044Part012
    + surrogateDiagTailX0RatChunk000Sub000Block044Part013
    + surrogateDiagTailX0RatChunk000Sub000Block044Part014
    + surrogateDiagTailX0RatChunk000Sub000Block044Part015
    + surrogateDiagTailX0RatChunk000Sub000Block044Part016
    + surrogateDiagTailX0RatChunk000Sub000Block044Part017
    + surrogateDiagTailX0RatChunk000Sub000Block044Part018
    + surrogateDiagTailX0RatChunk000Sub000Block044Part019
    + surrogateDiagTailX0RatChunk000Sub000Block044Part020
    + surrogateDiagTailX0RatChunk000Sub000Block044Part021
    + surrogateDiagTailX0RatChunk000Sub000Block044Part022
    + surrogateDiagTailX0RatChunk000Sub000Block044Part023
    + surrogateDiagTailX0RatChunk000Sub000Block044Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block044_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block044Head + surrogateDiagTailX0RatChunk000Sub000Block044Mid + surrogateDiagTailX0RatChunk000Sub000Block044Tail =
      surrogateDiagTailX0RatChunk000Sub000Block044 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block044Head surrogateDiagTailX0RatChunk000Sub000Block044Mid surrogateDiagTailX0RatChunk000Sub000Block044Tail surrogateDiagTailX0RatChunk000Sub000Block044
  ring

def SurrogateDiagonalTailChunk000Sub000Block044HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block044HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block044Head

def SurrogateDiagonalTailChunk000Sub000Block044MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block044MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block044Mid

def SurrogateDiagonalTailChunk000Sub000Block044TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block044TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block044Tail

theorem surrogateDiagonalTailChunk000Sub000Block044_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block044HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block044MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block044TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block044Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block044 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block044HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block044MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block044TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block044Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block044_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
